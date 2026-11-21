// Lean compiler output
// Module: Lean.Elab.Util
// Imports: public import Lean.Parser.Extension meta import Lean.Parser.Command public import Lean.KeyedDeclsAttribute import Lean.BuiltinDocAttr public import Lean.ExtraModUses import all Init.Prelude
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(lean_object*, lean_object*);
lean_object* l_EStateM_nonBacktrackable___redArg();
lean_object* l_EStateM_instMonadExceptOfOfBacktrackable___redArg(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRefPos___redArg(lean_object*, lean_object*);
lean_object* l_Lean_toMessageList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_recordExtraModUseFromDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_String_toFormat(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_equalScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_equalScope___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_expandOptNamedPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_expandOptNamedPrio___closed__0 = (const lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value;
static const lean_string_object l_Lean_Elab_expandOptNamedPrio___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_expandOptNamedPrio___closed__1 = (const lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value;
static const lean_string_object l_Lean_Elab_expandOptNamedPrio___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_expandOptNamedPrio___closed__2 = (const lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__2_value;
static const lean_string_object l_Lean_Elab_expandOptNamedPrio___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_expandOptNamedPrio___closed__3 = (const lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__3_value;
static const lean_ctor_object l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_expandOptNamedPrio___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_expandOptNamedPrio___closed__4 = (const lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "macroStack"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(63, 33, 22, 128, 67, 155, 63, 18)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "display macro expansion stack"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 212, 36, 208, 228, 94, 220, 119)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 94, 242, 78, 7, 86, 25, 134)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pp_macroStack;
static const lean_string_object l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0;
static lean_once_cell_t l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid syntax node kind `"};
static const lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0 = (const lean_object*)&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value;
static lean_once_cell_t l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
static const lean_string_object l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = (const lean_object*)&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value;
static lean_once_cell_t l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__0 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__1 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__2 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value;
static const lean_array_object l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__3 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__4 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__5 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__6 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__7 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__8 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__9 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__10;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__11;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__12 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__13 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__14 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__15 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__16;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__17;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__18;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__19;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__20;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__21;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__22;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__23;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__24;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__25;
static lean_once_cell_t l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkElabAttribute___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_mkElabAttribute___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_mkElabAttribute___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_mkElabAttribute___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " elaborator"};
static const lean_object* l_Lean_Elab_mkElabAttribute___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_mkElabAttribute___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "builtin_macro"};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 183, 24, 34, 89, 102, 112, 162)}};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 126, 236, 0, 202, 60, 1)}};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value;
static const lean_ctor_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "macroAttribute"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 124, 3, 111, 194, 84, 182, 133)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 390, .m_capacity = 390, .m_length = 387, .m_data = "Registers a macro expander for a given syntax node kind.\n\nA macro expander should have type `Lean.Macro` (which is `Lean.Syntax → Lean.MacroM Lean.Syntax`),\ni.e. should take syntax of the given syntax node kind as a parameter and produce different syntax\nin the same syntax category.\n\nThe `macro_rules` and `macro` commands should usually be preferred over using this attribute\ndirectly."};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(140) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_instMonadMacroAdapterCoreM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___closed__0 = (const lean_object*)&l_Lean_Elab_instMonadMacroAdapterCoreM___closed__0_value;
static const lean_closure_object l_Lean_Elab_instMonadMacroAdapterCoreM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___closed__1 = (const lean_object*)&l_Lean_Elab_instMonadMacroAdapterCoreM___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM;
LEAN_EXPORT uint8_t l_Lean_Elab_hasNameCollision___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_hasNameCollision___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_hasNameCollision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_hasNameCollision___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__23___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_liftMacroM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__3_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_liftMacroM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__4_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__5_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__1_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__2_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__6_value)}};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__7_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_liftMacroM___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__7_value),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_liftMacroM___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_liftMacroM___redArg___closed__10;
static lean_once_cell_t l_Lean_Elab_liftMacroM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_liftMacroM___redArg___closed__11;
static lean_once_cell_t l_Lean_Elab_liftMacroM___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_liftMacroM___redArg___closed__12;
static lean_once_cell_t l_Lean_Elab_liftMacroM___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_liftMacroM___redArg___closed__13;
static lean_once_cell_t l_Lean_Elab_liftMacroM___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_liftMacroM___redArg___closed__14;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_pure___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__9_value)} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_logException___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", errors "};
static const lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 78, 200, 72, 47, 79, 142, 191)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(255, 84, 221, 213, 184, 25, 230, 28)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 230, 224, 210, 33, 91, 167, 71)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(80, 51, 41, 220, 74, 50, 181, 52)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 155, 36, 75, 140, 113, 216, 4)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 108, 121, 158, 225, 216, 58, 115)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 130, 197, 179, 188, 68, 15, 67)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(151, 200, 117, 111, 119, 67, 77, 165)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 178, 137, 191, 232, 27, 150, 24)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2034298159) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 73, 120, 144, 106, 211, 68, 250)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 206, 183, 5, 147, 115, 55, 70)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 61, 92, 97, 132, 90, 23, 86)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(223, 154, 120, 49, 240, 44, 140, 147)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 235, 194, 189, 11, 11, 236, 225)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 235, 194, 189, 11, 11, 236, 225)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 13, 218, 138, 0, 214, 255, 58)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_prettyPrint(lean_object* v_stx_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
lean_inc(v_stx_1_);
v___x_2_ = l_Lean_Syntax_unsetTrailing(v_stx_1_);
v___x_3_ = l_Lean_Syntax_reprint(v___x_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = 0;
v___x_6_ = l_Lean_Syntax_formatStx(v_stx_1_, v___x_4_, v___x_5_);
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v___x_8_; 
lean_dec(v_stx_1_);
v_val_7_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_3_, 1);
v___x_8_ = l_String_toFormat(v_val_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format(lean_object* v_view_9_, lean_object* v_mainModule_10_){
_start:
{
lean_object* v___y_12_; lean_object* v_name_16_; lean_object* v_imported_17_; lean_object* v_ctx_18_; lean_object* v_scopes_19_; uint8_t v___x_20_; 
v_name_16_ = lean_ctor_get(v_view_9_, 0);
lean_inc(v_name_16_);
v_imported_17_ = lean_ctor_get(v_view_9_, 1);
lean_inc(v_imported_17_);
v_ctx_18_ = lean_ctor_get(v_view_9_, 2);
lean_inc(v_ctx_18_);
v_scopes_19_ = lean_ctor_get(v_view_9_, 3);
lean_inc(v_scopes_19_);
lean_dec_ref(v_view_9_);
v___x_20_ = l_List_isEmpty___redArg(v_scopes_19_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = lean_name_eq(v_ctx_18_, v_mainModule_10_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = l_Lean_Name_append(v_name_16_, v_imported_17_);
v___x_23_ = l_Lean_Name_append(v___x_22_, v_ctx_18_);
v___x_24_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(v___x_23_, v_scopes_19_);
v___y_12_ = v___x_24_;
goto v___jp_11_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_ctx_18_);
v___x_25_ = l_Lean_Name_append(v_name_16_, v_imported_17_);
v___x_26_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(v___x_25_, v_scopes_19_);
v___y_12_ = v___x_26_;
goto v___jp_11_;
}
}
else
{
lean_dec(v_scopes_19_);
lean_dec(v_ctx_18_);
lean_dec(v_imported_17_);
v___y_12_ = v_name_16_;
goto v___jp_11_;
}
v___jp_11_:
{
uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = 1;
v___x_14_ = l_Lean_Name_toString(v___y_12_, v___x_13_);
v___x_15_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_format___boxed(lean_object* v_view_27_, lean_object* v_mainModule_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_MacroScopesView_format(v_view_27_, v_mainModule_28_);
lean_dec(v_mainModule_28_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
if (lean_obj_tag(v_x_31_) == 0)
{
uint8_t v___x_32_; 
v___x_32_ = 1;
return v___x_32_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
}
else
{
if (lean_obj_tag(v_x_31_) == 0)
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v_head_37_; lean_object* v_tail_38_; uint8_t v___x_39_; 
v_head_35_ = lean_ctor_get(v_x_30_, 0);
v_tail_36_ = lean_ctor_get(v_x_30_, 1);
v_head_37_ = lean_ctor_get(v_x_31_, 0);
v_tail_38_ = lean_ctor_get(v_x_31_, 1);
v___x_39_ = lean_nat_dec_eq(v_head_35_, v_head_37_);
if (v___x_39_ == 0)
{
return v___x_39_;
}
else
{
v_x_30_ = v_tail_36_;
v_x_31_ = v_tail_38_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0___boxed(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_x_41_, v_x_42_);
lean_dec(v_x_42_);
lean_dec(v_x_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_equalScope(lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
lean_object* v_imported_47_; lean_object* v_ctx_48_; lean_object* v_scopes_49_; lean_object* v_imported_50_; lean_object* v_ctx_51_; lean_object* v_scopes_52_; uint8_t v___x_53_; 
v_imported_47_ = lean_ctor_get(v_a_45_, 1);
v_ctx_48_ = lean_ctor_get(v_a_45_, 2);
v_scopes_49_ = lean_ctor_get(v_a_45_, 3);
v_imported_50_ = lean_ctor_get(v_b_46_, 1);
v_ctx_51_ = lean_ctor_get(v_b_46_, 2);
v_scopes_52_ = lean_ctor_get(v_b_46_, 3);
v___x_53_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_scopes_49_, v_scopes_52_);
if (v___x_53_ == 0)
{
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = lean_name_eq(v_ctx_48_, v_ctx_51_);
if (v___x_54_ == 0)
{
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = lean_name_eq(v_imported_47_, v_imported_50_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_equalScope___boxed(lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_MacroScopesView_equalScope(v_a_56_, v_b_57_);
lean_dec_ref(v_b_57_);
lean_dec_ref(v_a_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object* v_stx_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = l_Lean_Syntax_isNone(v_stx_69_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Lean_Syntax_getArg(v_stx_69_, v___x_73_);
v___x_75_ = ((lean_object*)(l_Lean_Elab_expandOptNamedPrio___closed__4));
lean_inc(v___x_74_);
v___x_76_ = l_Lean_Syntax_isOfKind(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec(v___x_74_);
v___x_77_ = l_Lean_Macro_throwUnsupported___redArg(v_a_71_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(3u);
v___x_79_ = l_Lean_Syntax_getArg(v___x_74_, v___x_78_);
lean_dec(v___x_74_);
v___x_80_ = l_Lean_evalPrio(v___x_79_, v_a_70_, v_a_71_);
return v___x_80_;
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1000u);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_71_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object* v_stx_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_expandOptNamedPrio(v_stx_83_, v_a_84_, v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_stx_83_);
return v_res_86_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
if (lean_obj_tag(v_x_88_) == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 1;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
else
{
if (lean_obj_tag(v_x_88_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v_val_93_; uint8_t v_decide_94_; 
v_val_92_ = lean_ctor_get(v_x_87_, 0);
v_val_93_ = lean_ctor_get(v_x_88_, 0);
v_decide_94_ = lean_nat_dec_eq(v_val_92_, v_val_93_);
return v_decide_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(lean_object* v___x_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v_before_104_; uint8_t v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_head_102_ = lean_ctor_get(v_x_100_, 0);
v_tail_103_ = lean_ctor_get(v_x_100_, 1);
v_before_104_ = lean_ctor_get(v_head_102_, 0);
v___x_105_ = 0;
v___x_106_ = l_Lean_Syntax_getPos_x3f(v_before_104_, v___x_105_);
v___x_107_ = l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(v___x_106_, v___x_99_);
lean_dec(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_inc(v_head_102_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v_head_102_);
return v___x_108_;
}
else
{
v_x_100_ = v_tail_103_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(lean_object* v___x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec(v___x_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* v_ref_113_, lean_object* v_macroStack_114_){
_start:
{
uint8_t v___x_115_; lean_object* v___x_116_; 
v___x_115_ = 0;
v___x_116_ = l_Lean_Syntax_getPos_x3f(v_ref_113_, v___x_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_116_, v_macroStack_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_inc(v_ref_113_);
return v_ref_113_;
}
else
{
lean_object* v_val_118_; lean_object* v_before_119_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_117_, 1);
v_before_119_ = lean_ctor_get(v_val_118_, 0);
lean_inc(v_before_119_);
lean_dec(v_val_118_);
return v_before_119_;
}
}
else
{
lean_dec_ref_known(v___x_116_, 1);
lean_inc(v_ref_113_);
return v_ref_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* v_ref_120_, lean_object* v_macroStack_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Elab_getBetterRef(v_ref_120_, v_macroStack_121_);
lean_dec(v_macroStack_121_);
lean_dec(v_ref_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object* v_name_123_, lean_object* v_decl_124_, lean_object* v_ref_125_){
_start:
{
lean_object* v_defValue_127_; lean_object* v_descr_128_; lean_object* v_deprecation_x3f_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_defValue_127_ = lean_ctor_get(v_decl_124_, 0);
v_descr_128_ = lean_ctor_get(v_decl_124_, 1);
v_deprecation_x3f_129_ = lean_ctor_get(v_decl_124_, 2);
v___x_130_ = lean_alloc_ctor(1, 0, 1);
v___x_131_ = lean_unbox(v_defValue_127_);
lean_ctor_set_uint8(v___x_130_, 0, v___x_131_);
lean_inc(v_deprecation_x3f_129_);
lean_inc_ref(v_descr_128_);
lean_inc_n(v_name_123_, 2);
v___x_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_132_, 0, v_name_123_);
lean_ctor_set(v___x_132_, 1, v_ref_125_);
lean_ctor_set(v___x_132_, 2, v___x_130_);
lean_ctor_set(v___x_132_, 3, v_descr_128_);
lean_ctor_set(v___x_132_, 4, v_deprecation_x3f_129_);
v___x_133_ = lean_register_option(v_name_123_, v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v___x_133_, 0);
lean_dec(v_unused_142_);
v___x_135_ = v___x_133_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_dec(v___x_133_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_inc(v_defValue_127_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_name_123_);
lean_ctor_set(v___x_137_, 1, v_defValue_127_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_name_123_);
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_151_, lean_object* v_decl_152_, lean_object* v_ref_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_151_, v_decl_152_, v_ref_153_);
lean_dec_ref(v_decl_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_177_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_174_, v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
return v_res_179_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1));
v___x_184_ = l_Lean_MessageData_ofFormat(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0(lean_object* v___x_185_, lean_object* v_msgData_186_, lean_object* v_elem_187_){
_start:
{
lean_object* v_before_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_200_; 
v_before_188_ = lean_ctor_get(v_elem_187_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_elem_187_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_elem_187_, 1);
lean_dec(v_unused_201_);
v___x_190_ = v_elem_187_;
v_isShared_191_ = v_isSharedCheck_200_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_before_188_);
lean_dec(v_elem_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_200_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 7);
lean_ctor_set(v___x_190_, 1, v___x_185_);
lean_ctor_set(v___x_190_, 0, v_msgData_186_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_msgData_186_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_185_);
v___x_193_ = v_reuseFailAlloc_199_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2, &l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = l_Lean_MessageData_ofSyntax(v_before_188_);
v___x_197_ = l_Lean_indentD(v___x_196_);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_195_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(1);
v___x_203_ = l_Lean_MessageData_ofFormat(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___f_205_; 
v___x_204_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__0), 3, 1);
lean_closure_set(v___f_205_, 0, v___x_204_);
return v___f_205_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3));
v___x_210_ = l_Lean_MessageData_ofFormat(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_211_, lean_object* v_toPure_212_, lean_object* v_msgData_213_, lean_object* v_macroStack_214_, lean_object* v_____do__lift_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = l_Lean_Elab_pp_macroStack;
v___x_217_ = l_Lean_Option_get___redArg(v___x_211_, v_____do__lift_215_, v___x_216_);
v___x_218_ = lean_unbox(v___x_217_);
lean_dec(v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_macroStack_214_);
v___x_219_ = lean_apply_2(v_toPure_212_, lean_box(0), v_msgData_213_);
return v___x_219_;
}
else
{
if (lean_obj_tag(v_macroStack_214_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_apply_2(v_toPure_212_, lean_box(0), v_msgData_213_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_after_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_238_; 
v_head_221_ = lean_ctor_get(v_macroStack_214_, 0);
lean_inc(v_head_221_);
v_after_222_ = lean_ctor_get(v_head_221_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_head_221_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_head_221_, 0);
lean_dec(v_unused_239_);
v___x_224_ = v_head_221_;
v_isShared_225_ = v_isSharedCheck_238_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_after_222_);
lean_dec(v_head_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_238_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_229_; 
v___x_226_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_227_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 7);
lean_ctor_set(v___x_224_, 1, v___x_226_);
lean_ctor_set(v___x_224_, 0, v_msgData_213_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_msgData_213_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_226_);
v___x_229_ = v_reuseFailAlloc_237_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_msgData_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_MessageData_ofSyntax(v_after_222_);
v___x_233_ = l_Lean_indentD(v___x_232_);
v_msgData_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_234_, 0, v___x_231_);
lean_ctor_set(v_msgData_234_, 1, v___x_233_);
v___x_235_ = l_List_foldl___redArg(v___f_227_, v_msgData_234_, v_macroStack_214_);
v___x_236_ = lean_apply_2(v_toPure_212_, lean_box(0), v___x_235_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_240_, lean_object* v_toPure_241_, lean_object* v_msgData_242_, lean_object* v_macroStack_243_, lean_object* v_____do__lift_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_240_, v_toPure_241_, v_msgData_242_, v_macroStack_243_, v_____do__lift_244_);
lean_dec_ref(v_____do__lift_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_msgData_248_, lean_object* v_macroStack_249_){
_start:
{
lean_object* v___x_250_; lean_object* v_toApplicative_251_; lean_object* v_toBind_252_; lean_object* v_getOptions_253_; lean_object* v_toPure_254_; lean_object* v___f_255_; lean_object* v___x_256_; 
v___x_250_ = l_Lean_KVMap_instValueBool;
v_toApplicative_251_ = lean_ctor_get(v_inst_246_, 0);
lean_inc_ref(v_toApplicative_251_);
v_toBind_252_ = lean_ctor_get(v_inst_246_, 1);
lean_inc(v_toBind_252_);
lean_dec_ref(v_inst_246_);
v_getOptions_253_ = lean_ctor_get(v_inst_247_, 0);
lean_inc(v_getOptions_253_);
lean_dec_ref(v_inst_247_);
v_toPure_254_ = lean_ctor_get(v_toApplicative_251_, 1);
lean_inc(v_toPure_254_);
lean_dec_ref(v_toApplicative_251_);
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_255_, 0, v___x_250_);
lean_closure_set(v___f_255_, 1, v_toPure_254_);
lean_closure_set(v___f_255_, 2, v_msgData_248_);
lean_closure_set(v___f_255_, 3, v_macroStack_249_);
v___x_256_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v_getOptions_253_, v___f_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_msgData_260_, lean_object* v_macroStack_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Elab_addMacroStack___redArg(v_inst_258_, v_inst_259_, v_msgData_260_, v_macroStack_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_____r_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_270_ = l_Lean_throwError___redArg(v_inst_266_, v_inst_267_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_271_, lean_object* v___f_272_, lean_object* v_toPure_273_, lean_object* v_____do__lift_274_){
_start:
{
uint8_t v___x_275_; 
lean_inc(v_k_271_);
v___x_275_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_274_, v_k_271_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_toPure_273_);
lean_dec(v_k_271_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v___f_272_, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; 
lean_dec(v___f_272_);
v___x_278_ = lean_apply_2(v_toPure_273_, lean_box(0), v_k_271_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_279_, lean_object* v___f_280_, lean_object* v_toPure_281_, lean_object* v_toBind_282_, lean_object* v_getEnv_283_, lean_object* v_____do__lift_284_){
_start:
{
lean_object* v_k_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v_k_285_ = l_Lean_mkPrivateName(v_____do__lift_284_, v_k_279_);
v___f_286_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_286_, 0, v_k_285_);
lean_closure_set(v___f_286_, 1, v___f_280_);
lean_closure_set(v___f_286_, 2, v_toPure_281_);
v___x_287_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v_getEnv_283_, v___f_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_288_, lean_object* v___f_289_, lean_object* v_toPure_290_, lean_object* v_toBind_291_, lean_object* v_getEnv_292_, lean_object* v_____do__lift_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_288_, v___f_289_, v_toPure_290_, v_toBind_291_, v_getEnv_292_, v_____do__lift_293_);
lean_dec_ref(v_____do__lift_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_295_, lean_object* v_k_296_, lean_object* v_toBind_297_, lean_object* v_getEnv_298_, lean_object* v___f_299_, lean_object* v_____do__lift_300_){
_start:
{
uint8_t v_isExporting_304_; 
v_isExporting_304_ = lean_ctor_get_uint8(v_____do__lift_300_, sizeof(void*)*13);
if (v_isExporting_304_ == 0)
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_isPrivateName(v_k_296_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v___f_295_);
v___x_306_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v_getEnv_298_, v___f_299_);
return v___x_306_;
}
else
{
lean_dec(v___f_299_);
lean_dec(v_getEnv_298_);
lean_dec(v_toBind_297_);
goto v___jp_301_;
}
}
else
{
lean_dec(v___f_299_);
lean_dec(v_getEnv_298_);
lean_dec(v_toBind_297_);
goto v___jp_301_;
}
v___jp_301_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v___f_295_, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_307_, lean_object* v_k_308_, lean_object* v_toBind_309_, lean_object* v_getEnv_310_, lean_object* v___f_311_, lean_object* v_____do__lift_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_307_, v_k_308_, v_toBind_309_, v_getEnv_310_, v___f_311_, v_____do__lift_312_);
lean_dec_ref(v_____do__lift_312_);
lean_dec(v_k_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_314_, lean_object* v___f_315_, lean_object* v_toBind_316_, lean_object* v_getEnv_317_, lean_object* v___f_318_, lean_object* v_toPure_319_, lean_object* v_____do__lift_320_){
_start:
{
uint8_t v___x_321_; 
lean_inc(v_k_314_);
v___x_321_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_320_, v_k_314_);
if (v___x_321_ == 0)
{
lean_object* v___f_322_; lean_object* v___x_323_; 
lean_dec(v_toPure_319_);
lean_inc(v_getEnv_317_);
lean_inc(v_toBind_316_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_322_, 0, v___f_315_);
lean_closure_set(v___f_322_, 1, v_k_314_);
lean_closure_set(v___f_322_, 2, v_toBind_316_);
lean_closure_set(v___f_322_, 3, v_getEnv_317_);
lean_closure_set(v___f_322_, 4, v___f_318_);
v___x_323_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v_getEnv_317_, v___f_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v___f_318_);
lean_dec(v_getEnv_317_);
lean_dec(v_toBind_316_);
lean_dec(v___f_315_);
v___x_324_ = lean_apply_2(v_toPure_319_, lean_box(0), v_k_314_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_k_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_getEnv_331_; lean_object* v_toPure_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_325_, 0);
v_toBind_330_ = lean_ctor_get(v_inst_325_, 1);
lean_inc_n(v_toBind_330_, 3);
v_getEnv_331_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_n(v_getEnv_331_, 3);
lean_dec_ref(v_inst_326_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc_n(v_toPure_332_, 2);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_333_, 0, v_inst_325_);
lean_closure_set(v___f_333_, 1, v_inst_327_);
lean_inc_ref(v___f_333_);
lean_inc(v_k_328_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_334_, 0, v_k_328_);
lean_closure_set(v___f_334_, 1, v___f_333_);
lean_closure_set(v___f_334_, 2, v_toPure_332_);
lean_closure_set(v___f_334_, 3, v_toBind_330_);
lean_closure_set(v___f_334_, 4, v_getEnv_331_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_335_, 0, v_k_328_);
lean_closure_set(v___f_335_, 1, v___f_333_);
lean_closure_set(v___f_335_, 2, v_toBind_330_);
lean_closure_set(v___f_335_, 3, v_getEnv_331_);
lean_closure_set(v___f_335_, 4, v___f_334_);
lean_closure_set(v___f_335_, 5, v_toPure_332_);
v___x_336_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_getEnv_331_, v___f_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_k_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_338_, v_inst_339_, v_inst_340_, v_k_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_k_346_, lean_object* v_pre_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_343_, v_inst_344_, v_inst_345_, v_k_346_, v_pre_347_, v_x_348_);
lean_dec_ref(v_x_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_k_353_, lean_object* v_x_354_){
_start:
{
switch(lean_obj_tag(v_x_354_))
{
case 1:
{
lean_object* v_toMonadExceptOf_355_; lean_object* v_pre_356_; lean_object* v_tryCatch_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_toMonadExceptOf_355_ = lean_ctor_get(v_inst_352_, 0);
v_pre_356_ = lean_ctor_get(v_x_354_, 0);
v_tryCatch_357_ = lean_ctor_get(v_toMonadExceptOf_355_, 1);
lean_inc(v_tryCatch_357_);
lean_inc(v_pre_356_);
lean_inc(v_k_353_);
lean_inc_ref(v_inst_352_);
lean_inc_ref(v_inst_351_);
lean_inc_ref(v_inst_350_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_358_, 0, v_inst_350_);
lean_closure_set(v___f_358_, 1, v_inst_351_);
lean_closure_set(v___f_358_, 2, v_inst_352_);
lean_closure_set(v___f_358_, 3, v_k_353_);
lean_closure_set(v___f_358_, 4, v_pre_356_);
v___x_359_ = l_Lean_Name_append(v_x_354_, v_k_353_);
v___x_360_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_350_, v_inst_351_, v_inst_352_, v___x_359_);
v___x_361_ = lean_apply_3(v_tryCatch_357_, lean_box(0), v___x_360_, v___f_358_);
return v___x_361_;
}
case 0:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_350_, v_inst_351_, v_inst_352_, v_k_353_);
return v___x_362_;
}
default: 
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_x_354_);
lean_dec(v_k_353_);
lean_dec_ref(v_inst_351_);
v___x_363_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_364_ = l_Lean_throwError___redArg(v_inst_350_, v_inst_352_, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_k_368_, lean_object* v_pre_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_365_, v_inst_366_, v_inst_367_, v_k_368_, v_pre_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_k_376_, lean_object* v_x_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_373_, v_inst_374_, v_inst_375_, v_k_376_, v_x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_379_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v___x_383_);
lean_ctor_set(v___x_384_, 4, v___x_382_);
lean_ctor_set(v___x_384_, 5, v___x_382_);
lean_ctor_set(v___x_384_, 6, v___x_382_);
lean_ctor_set(v___x_384_, 7, v___x_382_);
lean_ctor_set(v___x_384_, 8, v___x_382_);
lean_ctor_set(v___x_384_, 9, v___x_382_);
lean_ctor_set(v___x_384_, 10, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_unsigned_to_nat(32u);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((size_t)5ULL);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_unsigned_to_nat(32u);
v___x_391_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_392_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_393_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_389_);
lean_ctor_set(v___x_393_, 3, v___x_389_);
lean_ctor_set_usize(v___x_393_, 4, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_box(1);
v___x_395_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_396_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_toCold_403_; lean_object* v_env_404_; lean_object* v_options_405_; uint8_t v___x_406_; lean_object* v_env_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_toCold_403_ = lean_ctor_get(v___y_399_, 0);
v_env_404_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_402_);
v_options_405_ = lean_ctor_get(v_toCold_403_, 2);
v___x_406_ = 0;
v_env_407_ = l_Lean_Environment_setRecordingDeps(v_env_404_, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_409_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_405_);
v___x_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_410_, 0, v_env_407_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
lean_ctor_set(v___x_410_, 3, v_options_405_);
v___x_411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_msgData_398_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_ref_422_ = lean_ctor_get(v___y_419_, 2);
v___x_423_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_418_, v___y_419_, v___y_420_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_inc(v_ref_422_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_ref_422_);
lean_ctor_set(v___x_428_, 1, v_a_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___x_447_; lean_object* v_env_448_; uint8_t v___x_449_; 
v___x_447_ = lean_st_ref_get(v___y_440_);
v_env_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_448_);
lean_dec(v___x_447_);
lean_inc(v_k_438_);
v___x_449_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_448_, v_k_438_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v_env_451_; uint8_t v_isExporting_452_; 
v___x_450_ = lean_st_ref_get(v___y_440_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_450_);
v_isExporting_452_ = lean_ctor_get_uint8(v_env_451_, sizeof(void*)*13);
lean_dec_ref(v_env_451_);
if (v_isExporting_452_ == 0)
{
uint8_t v___x_453_; 
v___x_453_ = l_Lean_isPrivateName(v_k_438_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v_k_456_; lean_object* v___x_457_; lean_object* v_env_458_; uint8_t v___x_459_; 
v___x_454_ = lean_st_ref_get(v___y_440_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v_k_456_ = l_Lean_mkPrivateName(v_env_455_, v_k_438_);
lean_dec_ref(v_env_455_);
v___x_457_ = lean_st_ref_get(v___y_440_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_458_);
lean_dec(v___x_457_);
lean_inc(v_k_456_);
v___x_459_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_458_, v_k_456_);
if (v___x_459_ == 0)
{
lean_dec(v_k_456_);
v___y_443_ = v___y_439_;
v___y_444_ = v___y_440_;
goto v___jp_442_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_k_456_);
return v___x_460_;
}
}
else
{
lean_dec(v_k_438_);
v___y_443_ = v___y_439_;
v___y_444_ = v___y_440_;
goto v___jp_442_;
}
}
else
{
lean_dec(v_k_438_);
v___y_443_ = v___y_439_;
v___y_444_ = v___y_440_;
goto v___jp_442_;
}
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_k_438_);
return v___x_461_;
}
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_446_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_445_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_467_, lean_object* v_x_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
switch(lean_obj_tag(v_x_468_))
{
case 1:
{
lean_object* v_pre_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_pre_472_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_pre_472_);
lean_inc(v_k_467_);
v___x_473_ = l_Lean_Name_append(v_x_468_, v_k_467_);
v___x_474_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_473_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec(v_pre_472_);
lean_dec(v_k_467_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; uint8_t v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v___x_476_ = l_Lean_Exception_isInterrupt(v_a_475_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
lean_inc(v_a_475_);
v___x_477_ = l_Lean_Exception_isRuntime(v_a_475_);
if (v___x_477_ == 0)
{
lean_dec_ref_known(v___x_474_, 1);
v_x_468_ = v_pre_472_;
goto _start;
}
else
{
lean_dec(v_pre_472_);
lean_dec(v_k_467_);
return v___x_474_;
}
}
else
{
lean_dec(v_pre_472_);
lean_dec(v_k_467_);
return v___x_474_;
}
}
}
case 0:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_467_, v___y_469_, v___y_470_);
return v___x_479_;
}
default: 
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_x_468_);
lean_dec(v_k_467_);
v___x_480_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_481_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_480_, v___y_469_, v___y_470_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_482_, v_x_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_toCold_492_; lean_object* v_currNamespace_493_; lean_object* v___x_494_; 
v_toCold_492_ = lean_ctor_get(v_a_489_, 0);
v_currNamespace_493_ = lean_ctor_get(v_toCold_492_, 4);
lean_inc(v_currNamespace_493_);
v___x_494_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_488_, v_currNamespace_493_, v_a_489_, v_a_490_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_500_, lean_object* v_msg_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_506_, v_msg_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_518_, lean_object* v_stx_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Attribute_Builtin_getId(v_stx_519_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_n(v_a_524_, 2);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_524_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_dec(v_a_524_);
lean_dec(v_defaultParserNamespace_518_);
return v___x_525_;
}
else
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v___x_527_ = l_Lean_Exception_isInterrupt(v_a_526_);
if (v___x_527_ == 0)
{
uint8_t v___x_528_; 
lean_inc(v_a_526_);
v___x_528_ = l_Lean_Exception_isRuntime(v_a_526_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref_known(v___x_525_, 1);
lean_inc(v_a_524_);
v___x_529_ = l_Lean_Name_append(v_defaultParserNamespace_518_, v_a_524_);
v___x_530_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_529_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec(v_a_524_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; uint8_t v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v___x_532_ = l_Lean_Exception_isInterrupt(v_a_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
lean_inc(v_a_531_);
v___x_533_ = l_Lean_Exception_isRuntime(v_a_531_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_530_, 1);
v___x_534_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_535_ = l_Lean_MessageData_ofName(v_a_524_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_538_, v_a_520_, v_a_521_);
return v___x_539_;
}
else
{
lean_dec(v_a_524_);
return v___x_530_;
}
}
else
{
lean_dec(v_a_524_);
return v___x_530_;
}
}
}
else
{
lean_dec(v_a_524_);
lean_dec(v_defaultParserNamespace_518_);
return v___x_525_;
}
}
else
{
lean_dec(v_a_524_);
lean_dec(v_defaultParserNamespace_518_);
return v___x_525_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_518_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_540_, lean_object* v_stx_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_540_, v_stx_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_550_, lean_object* v_opts_551_, lean_object* v_constName_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_554_ = l_Lean_Environment_evalConstCheck___redArg(v_env_550_, v_opts_551_, v___x_553_, v_constName_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_555_, lean_object* v_opts_556_, lean_object* v_constName_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_555_, v_opts_556_, v_constName_557_);
lean_dec_ref(v_opts_556_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_584_ = l_Lean_mkAtom(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_586_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_597_ = l_Lean_mkAtom(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_599_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_600_ = lean_array_push(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_602_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_603_ = lean_box(2);
v___x_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_606_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_607_ = lean_array_push(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_609_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_610_ = lean_box(2);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_613_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_616_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_617_ = lean_box(2);
v___x_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
lean_ctor_set(v___x_618_, 2, v___x_615_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_620_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_621_ = lean_array_push(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_623_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_624_ = lean_box(2);
v___x_625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_627_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_628_ = lean_array_push(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_630_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_631_ = lean_box(2);
v___x_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_629_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_634_, lean_object* v_declName_635_, lean_object* v_kind_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
if (v_builtin_634_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_declName_635_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_635_, v___y_637_, v___y_638_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_643_, lean_object* v_declName_644_, lean_object* v_kind_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v_builtin_boxed_649_; lean_object* v_res_650_; 
v_builtin_boxed_649_ = lean_unbox(v_builtin_643_);
v_res_650_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_649_, v_declName_644_, v_kind_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v_kind_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_infoState_655_; uint8_t v_enabled_656_; 
v___x_654_ = lean_st_ref_get(v___y_652_);
v_infoState_655_ = lean_ctor_get(v___x_654_, 8);
lean_inc_ref(v_infoState_655_);
lean_dec(v___x_654_);
v_enabled_656_ = lean_ctor_get_uint8(v_infoState_655_, sizeof(void*)*3);
lean_dec_ref(v_infoState_655_);
if (v_enabled_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v_t_651_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v_infoState_660_; lean_object* v_env_661_; lean_object* v_nextMacroScope_662_; lean_object* v_ngen_663_; lean_object* v_auxDeclNGen_664_; lean_object* v_traceState_665_; lean_object* v_cache_666_; lean_object* v_recordedDeps_667_; lean_object* v_messages_668_; lean_object* v_snapshotTasks_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_691_; 
v___x_659_ = lean_st_ref_take(v___y_652_);
v_infoState_660_ = lean_ctor_get(v___x_659_, 8);
v_env_661_ = lean_ctor_get(v___x_659_, 0);
v_nextMacroScope_662_ = lean_ctor_get(v___x_659_, 1);
v_ngen_663_ = lean_ctor_get(v___x_659_, 2);
v_auxDeclNGen_664_ = lean_ctor_get(v___x_659_, 3);
v_traceState_665_ = lean_ctor_get(v___x_659_, 4);
v_cache_666_ = lean_ctor_get(v___x_659_, 5);
v_recordedDeps_667_ = lean_ctor_get(v___x_659_, 6);
v_messages_668_ = lean_ctor_get(v___x_659_, 7);
v_snapshotTasks_669_ = lean_ctor_get(v___x_659_, 9);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_691_ == 0)
{
v___x_671_ = v___x_659_;
v_isShared_672_ = v_isSharedCheck_691_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snapshotTasks_669_);
lean_inc(v_infoState_660_);
lean_inc(v_messages_668_);
lean_inc(v_recordedDeps_667_);
lean_inc(v_cache_666_);
lean_inc(v_traceState_665_);
lean_inc(v_auxDeclNGen_664_);
lean_inc(v_ngen_663_);
lean_inc(v_nextMacroScope_662_);
lean_inc(v_env_661_);
lean_dec(v___x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_691_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
uint8_t v_enabled_673_; lean_object* v_assignment_674_; lean_object* v_lazyAssignment_675_; lean_object* v_trees_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_690_; 
v_enabled_673_ = lean_ctor_get_uint8(v_infoState_660_, sizeof(void*)*3);
v_assignment_674_ = lean_ctor_get(v_infoState_660_, 0);
v_lazyAssignment_675_ = lean_ctor_get(v_infoState_660_, 1);
v_trees_676_ = lean_ctor_get(v_infoState_660_, 2);
v_isSharedCheck_690_ = !lean_is_exclusive(v_infoState_660_);
if (v_isSharedCheck_690_ == 0)
{
v___x_678_ = v_infoState_660_;
v_isShared_679_ = v_isSharedCheck_690_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_trees_676_);
lean_inc(v_lazyAssignment_675_);
lean_inc(v_assignment_674_);
lean_dec(v_infoState_660_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_690_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Lean_PersistentArray_push___redArg(v_trees_676_, v_t_651_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 2, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_assignment_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_lazyAssignment_675_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___x_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_689_, sizeof(void*)*3, v_enabled_673_);
v___x_683_ = v_reuseFailAlloc_689_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 8, v___x_683_);
v___x_685_ = v___x_671_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_env_661_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_nextMacroScope_662_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_ngen_663_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_auxDeclNGen_664_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_traceState_665_);
lean_ctor_set(v_reuseFailAlloc_688_, 5, v_cache_666_);
lean_ctor_set(v_reuseFailAlloc_688_, 6, v_recordedDeps_667_);
lean_ctor_set(v_reuseFailAlloc_688_, 7, v_messages_668_);
lean_ctor_set(v_reuseFailAlloc_688_, 8, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_688_, 9, v_snapshotTasks_669_);
v___x_685_ = v_reuseFailAlloc_688_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_st_ref_put(v___y_652_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_680_);
return v___x_687_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_692_, v___y_693_);
lean_dec(v___y_693_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(32u);
v___x_697_ = lean_mk_empty_array_with_capacity(v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_699_ = ((size_t)5ULL);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_unsigned_to_nat(32u);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_701_);
v___x_703_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_700_);
lean_ctor_set(v___x_704_, 3, v___x_700_);
lean_ctor_set_usize(v___x_704_, 4, v___x_699_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; lean_object* v_infoState_710_; uint8_t v_enabled_711_; 
v___x_709_ = lean_st_ref_get(v___y_707_);
v_infoState_710_ = lean_ctor_get(v___x_709_, 8);
lean_inc_ref(v_infoState_710_);
lean_dec(v___x_709_);
v_enabled_711_ = lean_ctor_get_uint8(v_infoState_710_, sizeof(void*)*3);
lean_dec_ref(v_infoState_710_);
if (v_enabled_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v_t_705_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_715_, 0, v_t_705_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_715_, v___y_707_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_721_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_733_ = l_Lean_stringToMessageData(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_736_ = l_Lean_stringToMessageData(v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__14));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__16));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__18));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__20));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_755_, lean_object* v_declHint_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_env_761_; uint8_t v___x_762_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_st_ref_get(v___y_757_);
v_env_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_env_761_);
lean_dec(v___x_760_);
v___x_762_ = l_Lean_Name_isAnonymous(v_declHint_756_);
if (v___x_762_ == 0)
{
uint8_t v_isExporting_763_; 
v_isExporting_763_ = lean_ctor_get_uint8(v_env_761_, sizeof(void*)*13);
if (v_isExporting_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v_env_761_);
lean_dec(v_declHint_756_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v_msg_755_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; uint8_t v___x_766_; 
lean_inc_ref(v_env_761_);
v___x_765_ = l_Lean_Environment_setExporting(v_env_761_, v___x_762_);
lean_inc(v_declHint_756_);
lean_inc_ref(v___x_765_);
v___x_766_ = l_Lean_Environment_contains(v___x_765_, v_declHint_756_, v_isExporting_763_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v___x_765_);
lean_dec_ref(v_env_761_);
lean_dec(v_declHint_756_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_msg_755_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_c_773_; lean_object* v___x_774_; 
v___x_768_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_769_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_770_ = l_Lean_Options_empty;
lean_inc_ref(v___x_765_);
v___x_771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_771_, 0, v___x_765_);
lean_ctor_set(v___x_771_, 1, v___x_768_);
lean_ctor_set(v___x_771_, 2, v___x_769_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
lean_inc(v_declHint_756_);
v___x_772_ = l_Lean_MessageData_ofConstName(v_declHint_756_, v___x_762_);
v_c_773_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_773_, 0, v___x_771_);
lean_ctor_set(v_c_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_765_, v_declHint_756_);
lean_dec_ref(v___x_765_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_env_761_);
lean_dec(v_declHint_756_);
v___x_775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_c_773_);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_MessageData_note(v___x_778_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v_msg_755_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_835_; 
v_val_782_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_835_ == 0)
{
v___x_784_ = v___x_774_;
v_isShared_785_ = v_isSharedCheck_835_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v___x_774_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_835_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v_modules_787_; lean_object* v_moduleNames_788_; lean_object* v_mod_789_; uint8_t v___x_804_; 
v___x_786_ = l_Lean_Environment_header(v_env_761_);
lean_dec_ref(v_env_761_);
v_modules_787_ = lean_ctor_get(v___x_786_, 3);
lean_inc_ref(v_modules_787_);
v_moduleNames_788_ = lean_ctor_get(v___x_786_, 4);
lean_inc_ref(v_moduleNames_788_);
lean_dec_ref(v___x_786_);
v_mod_789_ = lean_array_get(v___x_759_, v_moduleNames_788_, v_val_782_);
lean_dec_ref(v_moduleNames_788_);
v___x_804_ = l_Lean_isPrivateName(v_declHint_756_);
lean_dec(v_declHint_756_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_modules_787_);
v___x_806_ = lean_nat_dec_lt(v_val_782_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec_ref(v_modules_787_);
lean_dec(v_val_782_);
goto v___jp_790_;
}
else
{
lean_object* v___x_807_; lean_object* v_toImport_808_; uint8_t v_isExported_809_; 
v___x_807_ = lean_array_fget(v_modules_787_, v_val_782_);
lean_dec(v_val_782_);
lean_dec_ref(v_modules_787_);
v_toImport_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc_ref(v_toImport_808_);
lean_dec(v___x_807_);
v_isExported_809_ = lean_ctor_get_uint8(v_toImport_808_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_808_);
if (v_isExported_809_ == 0)
{
goto v___jp_790_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_784_);
v___x_810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_c_773_);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_MessageData_ofName(v_mod_789_);
lean_inc_ref(v___x_814_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_814_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_MessageData_note(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v_msg_755_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v_modules_787_);
lean_del_object(v___x_784_);
lean_dec(v_val_782_);
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_c_773_);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_MessageData_ofName(v_mod_789_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_MessageData_note(v___x_831_);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v_msg_755_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_c_773_);
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_MessageData_ofName(v_mod_789_);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_MessageData_note(v___x_798_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v_msg_755_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
lean_ctor_set(v___x_784_, 0, v___x_800_);
v___x_802_ = v___x_784_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec_ref(v_env_761_);
lean_dec(v_declHint_756_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_msg_755_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_837_, lean_object* v_declHint_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_837_, v_declHint_838_, v___y_839_);
lean_dec(v___y_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_842_, lean_object* v_declHint_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_857_; 
v___x_847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_842_, v_declHint_843_, v___y_845_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = l_Lean_unknownIdentifierMessageTag;
v___x_853_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_858_, lean_object* v_declHint_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_858_, v_declHint_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_864_, lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_toCold_869_; lean_object* v_currRecDepth_870_; lean_object* v_ref_871_; uint16_t v_optionFlags_872_; uint8_t v_suppressElabErrors_873_; uint8_t v_checkDeprecated_874_; uint8_t v_isRecordingDeps_875_; lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_toCold_869_ = lean_ctor_get(v___y_866_, 0);
v_currRecDepth_870_ = lean_ctor_get(v___y_866_, 1);
v_ref_871_ = lean_ctor_get(v___y_866_, 2);
v_optionFlags_872_ = lean_ctor_get_uint16(v___y_866_, sizeof(void*)*3);
v_suppressElabErrors_873_ = lean_ctor_get_uint8(v___y_866_, sizeof(void*)*3 + 2);
v_checkDeprecated_874_ = lean_ctor_get_uint8(v___y_866_, sizeof(void*)*3 + 3);
v_isRecordingDeps_875_ = lean_ctor_get_uint8(v___y_866_, sizeof(void*)*3 + 4);
v_ref_876_ = l_Lean_replaceRef(v_ref_864_, v_ref_871_);
lean_inc(v_currRecDepth_870_);
lean_inc_ref(v_toCold_869_);
v___x_877_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_877_, 0, v_toCold_869_);
lean_ctor_set(v___x_877_, 1, v_currRecDepth_870_);
lean_ctor_set(v___x_877_, 2, v_ref_876_);
lean_ctor_set_uint16(v___x_877_, sizeof(void*)*3, v_optionFlags_872_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 2, v_suppressElabErrors_873_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 3, v_checkDeprecated_874_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 4, v_isRecordingDeps_875_);
v___x_878_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_865_, v___x_877_, v___y_867_);
lean_dec_ref_known(v___x_877_, 3);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_879_, v_msg_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v_ref_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_885_, lean_object* v_msg_886_, lean_object* v_declHint_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_893_; 
v___x_891_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_886_, v_declHint_887_, v___y_888_, v___y_889_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
v___x_893_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_885_, v_a_892_, v___y_888_, v___y_889_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_894_, lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_894_, v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v_ref_894_);
return v_res_900_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_904_, lean_object* v_constName_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_909_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_910_ = 0;
lean_inc(v_constName_905_);
v___x_911_ = l_Lean_MessageData_ofConstName(v_constName_905_, v___x_910_);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_909_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_904_, v___x_914_, v_constName_905_, v___y_906_, v___y_907_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_916_, lean_object* v_constName_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_916_, v_constName_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v_ref_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_ref_926_; lean_object* v___x_927_; 
v_ref_926_ = lean_ctor_get(v___y_923_, 2);
v___x_927_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_926_, v_constName_922_, v___y_923_, v___y_924_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v_env_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_st_ref_get(v___y_935_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_938_);
lean_dec(v___x_937_);
v___x_939_ = 0;
lean_inc(v_constName_933_);
v___x_940_ = l_Lean_Environment_findConstVal_x3f(v_env_938_, v_constName_933_, v___x_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_933_, v___y_934_, v___y_935_);
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_constName_933_);
v_val_942_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
if (lean_obj_tag(v_a_955_) == 0)
{
lean_object* v___x_957_; 
v___x_957_ = l_List_reverse___redArg(v_a_956_);
return v___x_957_;
}
else
{
lean_object* v_head_958_; lean_object* v_tail_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_968_; 
v_head_958_ = lean_ctor_get(v_a_955_, 0);
v_tail_959_ = lean_ctor_get(v_a_955_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_968_ == 0)
{
v___x_961_ = v_a_955_;
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_tail_959_);
lean_inc(v_head_958_);
lean_dec(v_a_955_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Lean_mkLevelParam(v_head_958_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_a_956_);
lean_ctor_set(v___x_961_, 0, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_956_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_a_955_ = v_tail_959_;
v_a_956_ = v___x_965_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
lean_inc(v_constName_969_);
v___x_973_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_985_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_985_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_levelParams_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v_levelParams_978_ = lean_ctor_get(v_a_974_, 1);
lean_inc(v_levelParams_978_);
lean_dec(v_a_974_);
v___x_979_ = lean_box(0);
v___x_980_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_978_, v___x_979_);
v___x_981_ = l_Lean_mkConst(v_constName_969_, v___x_980_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_981_);
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_constName_969_);
v_a_986_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_973_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_973_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_999_, lean_object* v_n_1000_, lean_object* v_expectedType_x3f_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_1000_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_stx_999_);
v___x_1009_ = l_Lean_LocalContext_empty;
v___x_1010_ = 0;
v___x_1011_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1011_, 0, v___x_1008_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v_expectedType_x3f_1001_);
lean_ctor_set(v___x_1011_, 3, v_a_1006_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*4, v___x_1010_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*4 + 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1012_, v___y_1002_, v___y_1003_);
return v___x_1013_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_expectedType_x3f_1001_);
lean_dec(v_stx_999_);
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1022_, lean_object* v_n_1023_, lean_object* v_expectedType_x3f_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1022_, v_n_1023_, v_expectedType_x3f_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0(lean_object* v___x_1029_, lean_object* v_entry_1030_, lean_object* v_s_1031_){
_start:
{
lean_object* v_addEntryFn_1032_; lean_object* v_importedEntries_1033_; lean_object* v_state_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_addEntryFn_1032_ = lean_ctor_get(v___x_1029_, 3);
lean_inc(v_addEntryFn_1032_);
lean_dec_ref(v___x_1029_);
v_importedEntries_1033_ = lean_ctor_get(v_s_1031_, 0);
v_state_1034_ = lean_ctor_get(v_s_1031_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_s_1031_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v_s_1031_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_state_1034_);
lean_inc(v_importedEntries_1033_);
lean_dec(v_s_1031_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_state_1038_; lean_object* v___x_1040_; 
v_state_1038_ = lean_apply_2(v_addEntryFn_1032_, v_state_1034_, v_entry_1030_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_state_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_importedEntries_1033_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_state_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_array_get_size(v_keys_1043_);
v___x_1047_ = lean_nat_dec_lt(v_i_1044_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec(v_i_1044_);
return v___x_1047_;
}
else
{
lean_object* v_k_x27_1048_; uint8_t v___x_1049_; 
v_k_x27_1048_ = lean_array_fget_borrowed(v_keys_1043_, v_i_1044_);
v___x_1049_ = l_Lean_instBEqExtraModUse_beq(v_k_1045_, v_k_x27_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_i_1044_, v___x_1050_);
lean_dec(v_i_1044_);
v_i_1044_ = v___x_1051_;
goto _start;
}
else
{
lean_dec(v_i_1044_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1053_, v_i_1054_, v_k_1055_);
lean_dec_ref(v_k_1055_);
lean_dec_ref(v_keys_1053_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1058_, size_t v_x_1059_, lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1058_) == 0)
{
lean_object* v_es_1061_; lean_object* v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; lean_object* v_j_1065_; lean_object* v___x_1066_; 
v_es_1061_ = lean_ctor_get(v_x_1058_, 0);
v___x_1062_ = lean_box(2);
v___x_1063_ = ((size_t)31ULL);
v___x_1064_ = lean_usize_land(v_x_1059_, v___x_1063_);
v_j_1065_ = lean_usize_to_nat(v___x_1064_);
v___x_1066_ = lean_array_get_borrowed(v___x_1062_, v_es_1061_, v_j_1065_);
lean_dec(v_j_1065_);
switch(lean_obj_tag(v___x_1066_))
{
case 0:
{
lean_object* v_key_1067_; uint8_t v___x_1068_; 
v_key_1067_ = lean_ctor_get(v___x_1066_, 0);
v___x_1068_ = l_Lean_instBEqExtraModUse_beq(v_x_1060_, v_key_1067_);
return v___x_1068_;
}
case 1:
{
lean_object* v_node_1069_; size_t v___x_1070_; size_t v___x_1071_; 
v_node_1069_ = lean_ctor_get(v___x_1066_, 0);
v___x_1070_ = ((size_t)5ULL);
v___x_1071_ = lean_usize_shift_right(v_x_1059_, v___x_1070_);
v_x_1058_ = v_node_1069_;
v_x_1059_ = v___x_1071_;
goto _start;
}
default: 
{
uint8_t v___x_1073_; 
v___x_1073_ = 0;
return v___x_1073_;
}
}
}
else
{
lean_object* v_ks_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_ks_1074_ = lean_ctor_get(v_x_1058_, 0);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1074_, v___x_1075_, v_x_1060_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
size_t v_x_6751__boxed_1080_; uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_x_6751__boxed_1080_ = lean_unbox_usize(v_x_1078_);
lean_dec(v_x_1078_);
v_res_1081_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1077_, v_x_6751__boxed_1080_, v_x_1079_);
lean_dec_ref(v_x_1079_);
lean_dec_ref(v_x_1077_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint64_t v___x_1085_; size_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = l_Lean_instHashableExtraModUse_hash(v_x_1084_);
v___x_1086_ = lean_uint64_to_usize(v___x_1085_);
v___x_1087_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1083_, v___x_1086_, v_x_1084_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1088_, v_x_1089_);
lean_dec_ref(v_x_1089_);
lean_dec_ref(v_x_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1092_; double v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_float_of_nat(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1097_, lean_object* v_msg_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_ref_1102_; lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1149_; 
v_ref_1102_ = lean_ctor_get(v___y_1099_, 2);
v___x_1103_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1098_, v___y_1099_, v___y_1100_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1149_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1149_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v_traceState_1109_; lean_object* v_env_1110_; lean_object* v_nextMacroScope_1111_; lean_object* v_ngen_1112_; lean_object* v_auxDeclNGen_1113_; lean_object* v_cache_1114_; lean_object* v_recordedDeps_1115_; lean_object* v_messages_1116_; lean_object* v_infoState_1117_; lean_object* v_snapshotTasks_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1148_; 
v___x_1108_ = lean_st_ref_take(v___y_1100_);
v_traceState_1109_ = lean_ctor_get(v___x_1108_, 4);
v_env_1110_ = lean_ctor_get(v___x_1108_, 0);
v_nextMacroScope_1111_ = lean_ctor_get(v___x_1108_, 1);
v_ngen_1112_ = lean_ctor_get(v___x_1108_, 2);
v_auxDeclNGen_1113_ = lean_ctor_get(v___x_1108_, 3);
v_cache_1114_ = lean_ctor_get(v___x_1108_, 5);
v_recordedDeps_1115_ = lean_ctor_get(v___x_1108_, 6);
v_messages_1116_ = lean_ctor_get(v___x_1108_, 7);
v_infoState_1117_ = lean_ctor_get(v___x_1108_, 8);
v_snapshotTasks_1118_ = lean_ctor_get(v___x_1108_, 9);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1120_ = v___x_1108_;
v_isShared_1121_ = v_isSharedCheck_1148_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_snapshotTasks_1118_);
lean_inc(v_infoState_1117_);
lean_inc(v_messages_1116_);
lean_inc(v_recordedDeps_1115_);
lean_inc(v_cache_1114_);
lean_inc(v_traceState_1109_);
lean_inc(v_auxDeclNGen_1113_);
lean_inc(v_ngen_1112_);
lean_inc(v_nextMacroScope_1111_);
lean_inc(v_env_1110_);
lean_dec(v___x_1108_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1148_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint64_t v_tid_1122_; lean_object* v_traces_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1147_; 
v_tid_1122_ = lean_ctor_get_uint64(v_traceState_1109_, sizeof(void*)*1);
v_traces_1123_ = lean_ctor_get(v_traceState_1109_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_traceState_1109_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1125_ = v_traceState_1109_;
v_isShared_1126_ = v_isSharedCheck_1147_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_traces_1123_);
lean_dec(v_traceState_1109_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1147_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; double v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1130_ = 0;
v___x_1131_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1132_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1132_, 0, v_cls_1097_);
lean_ctor_set(v___x_1132_, 1, v___x_1128_);
lean_ctor_set(v___x_1132_, 2, v___x_1131_);
lean_ctor_set_float(v___x_1132_, sizeof(void*)*3, v___x_1129_);
lean_ctor_set_float(v___x_1132_, sizeof(void*)*3 + 8, v___x_1129_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*3 + 16, v___x_1130_);
v___x_1133_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1134_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v_a_1104_);
lean_ctor_set(v___x_1134_, 2, v___x_1133_);
lean_inc(v_ref_1102_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_ref_1102_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_PersistentArray_push___redArg(v_traces_1123_, v___x_1135_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1136_);
v___x_1138_ = v___x_1125_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1136_);
lean_ctor_set_uint64(v_reuseFailAlloc_1146_, sizeof(void*)*1, v_tid_1122_);
v___x_1138_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1138_);
v___x_1140_ = v___x_1120_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_env_1110_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_nextMacroScope_1111_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_ngen_1112_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_auxDeclNGen_1113_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1145_, 5, v_cache_1114_);
lean_ctor_set(v_reuseFailAlloc_1145_, 6, v_recordedDeps_1115_);
lean_ctor_set(v_reuseFailAlloc_1145_, 7, v_messages_1116_);
lean_ctor_set(v_reuseFailAlloc_1145_, 8, v_infoState_1117_);
lean_ctor_set(v_reuseFailAlloc_1145_, 9, v_snapshotTasks_1118_);
v___x_1140_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_st_ref_put(v___y_1100_, v___x_1140_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1127_);
v___x_1143_ = v___x_1106_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1127_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1150_, lean_object* v_msg_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1150_, v_msg_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1160_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1169_ = l_Lean_stringToMessageData(v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v_cls_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_cls_1175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1177_ = l_Lean_Name_append(v___x_1176_, v_cls_1175_);
return v___x_1177_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1180_ = l_Lean_stringToMessageData(v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1183_ = l_Lean_stringToMessageData(v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1188_, uint8_t v_isMeta_1189_, lean_object* v_hint_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_env_1212_; uint8_t v_isExporting_1213_; lean_object* v_entry_1214_; lean_object* v___x_1215_; lean_object* v_env_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
v___x_1211_ = lean_st_ref_get(v___y_1192_);
v_env_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_env_1212_);
lean_dec(v___x_1211_);
v_isExporting_1213_ = lean_ctor_get_uint8(v_env_1212_, sizeof(void*)*13);
lean_dec_ref(v_env_1212_);
lean_inc(v_mod_1188_);
v_entry_1214_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1214_, 0, v_mod_1188_);
lean_ctor_set_uint8(v_entry_1214_, sizeof(void*)*1, v_isExporting_1213_);
lean_ctor_set_uint8(v_entry_1214_, sizeof(void*)*1 + 1, v_isMeta_1189_);
v___x_1215_ = lean_st_ref_get(v___y_1192_);
v_env_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_ref(v_env_1216_);
lean_dec(v___x_1215_);
v___x_1217_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1218_ = lean_box(1);
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1210_, v___x_1217_, v_env_1216_, v___x_1218_, v___x_1219_);
v___x_1221_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1220_, v_entry_1214_);
lean_dec(v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v_toCold_1222_; lean_object* v_options_1223_; lean_object* v_inheritedTraceOptions_1224_; uint8_t v_hasTrace_1225_; lean_object* v___f_1226_; uint8_t v___x_1227_; lean_object* v___y_1229_; 
v_toCold_1222_ = lean_ctor_get(v___y_1191_, 0);
v_options_1223_ = lean_ctor_get(v_toCold_1222_, 2);
v_inheritedTraceOptions_1224_ = lean_ctor_get(v_toCold_1222_, 11);
v_hasTrace_1225_ = lean_ctor_get_uint8(v_options_1223_, sizeof(void*)*1);
v___f_1226_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_1226_, 0, v___x_1217_);
lean_closure_set(v___f_1226_, 1, v_entry_1214_);
v___x_1227_ = 1;
if (v_hasTrace_1225_ == 0)
{
lean_dec(v_hint_1190_);
lean_dec(v_mod_1188_);
v___y_1229_ = v___y_1192_;
goto v___jp_1228_;
}
else
{
lean_object* v_cls_1247_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_cls_1247_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1267_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___x_1268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1224_, v_options_1223_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v_hint_1190_);
lean_dec(v_mod_1188_);
v___y_1229_ = v___y_1192_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1269_; lean_object* v___y_1271_; 
v___x_1269_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1213_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1271_ = v___x_1278_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1271_ = v___x_1279_;
goto v___jp_1270_;
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v___y_1271_);
v___x_1272_ = l_Lean_stringToMessageData(v___y_1271_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1269_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
if (v_isMeta_1189_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1254_ = v___x_1275_;
v___y_1255_ = v___x_1276_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1254_ = v___x_1275_;
v___y_1255_ = v___x_1277_;
goto v___jp_1253_;
}
}
}
v___jp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___y_1249_);
lean_ctor_set(v___x_1251_, 1, v___y_1250_);
v___x_1252_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1247_, v___x_1251_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref_known(v___x_1252_, 1);
v___y_1229_ = v___y_1192_;
goto v___jp_1228_;
}
else
{
lean_dec_ref(v___f_1226_);
return v___x_1252_;
}
}
v___jp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
lean_inc_ref(v___y_1255_);
v___x_1256_ = l_Lean_stringToMessageData(v___y_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_MessageData_ofName(v_mod_1188_);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_Name_isAnonymous(v_hint_1190_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8);
v___x_1264_ = l_Lean_MessageData_ofName(v_hint_1190_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___y_1249_ = v___x_1261_;
v___y_1250_ = v___x_1265_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_hint_1190_);
v___x_1266_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___y_1249_ = v___x_1261_;
v___y_1250_ = v___x_1266_;
goto v___jp_1248_;
}
}
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v_toEnvExtension_1231_; lean_object* v_env_1232_; lean_object* v_nextMacroScope_1233_; lean_object* v_ngen_1234_; lean_object* v_auxDeclNGen_1235_; lean_object* v_traceState_1236_; lean_object* v_recordedDeps_1237_; lean_object* v_messages_1238_; lean_object* v_infoState_1239_; lean_object* v_snapshotTasks_1240_; lean_object* v_asyncMode_1241_; uint8_t v_logWrites_1242_; lean_object* v___x_1243_; 
v___x_1230_ = lean_st_ref_take(v___y_1229_);
v_toEnvExtension_1231_ = lean_ctor_get(v___x_1217_, 0);
v_env_1232_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref(v_env_1232_);
v_nextMacroScope_1233_ = lean_ctor_get(v___x_1230_, 1);
lean_inc(v_nextMacroScope_1233_);
v_ngen_1234_ = lean_ctor_get(v___x_1230_, 2);
lean_inc_ref(v_ngen_1234_);
v_auxDeclNGen_1235_ = lean_ctor_get(v___x_1230_, 3);
lean_inc_ref(v_auxDeclNGen_1235_);
v_traceState_1236_ = lean_ctor_get(v___x_1230_, 4);
lean_inc_ref(v_traceState_1236_);
v_recordedDeps_1237_ = lean_ctor_get(v___x_1230_, 6);
lean_inc_ref(v_recordedDeps_1237_);
v_messages_1238_ = lean_ctor_get(v___x_1230_, 7);
lean_inc_ref(v_messages_1238_);
v_infoState_1239_ = lean_ctor_get(v___x_1230_, 8);
lean_inc_ref(v_infoState_1239_);
v_snapshotTasks_1240_ = lean_ctor_get(v___x_1230_, 9);
lean_inc_ref(v_snapshotTasks_1240_);
lean_dec(v___x_1230_);
v_asyncMode_1241_ = lean_ctor_get(v_toEnvExtension_1231_, 2);
v_logWrites_1242_ = lean_ctor_get_uint8(v_toEnvExtension_1231_, sizeof(void*)*6);
v___x_1243_ = lean_box(0);
if (v_logWrites_1242_ == 0)
{
lean_object* v___x_1244_; 
lean_inc_ref(v_toEnvExtension_1231_);
v___x_1244_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1231_, v_env_1232_, v___f_1226_, v_asyncMode_1241_, v___x_1219_, v___x_1227_);
v___y_1195_ = v_auxDeclNGen_1235_;
v___y_1196_ = v___x_1243_;
v___y_1197_ = v_ngen_1234_;
v___y_1198_ = v_traceState_1236_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v_recordedDeps_1237_;
v___y_1201_ = v_snapshotTasks_1240_;
v___y_1202_ = v_nextMacroScope_1233_;
v___y_1203_ = v_messages_1238_;
v___y_1204_ = v_infoState_1239_;
v___y_1205_ = v___x_1244_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_inc_ref_n(v_toEnvExtension_1231_, 2);
v___x_1245_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1231_, v_env_1232_);
lean_dec_ref(v_env_1232_);
v___x_1246_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1231_, v___x_1245_, v___f_1226_, v_asyncMode_1241_, v___x_1219_, v___x_1227_);
v___y_1195_ = v_auxDeclNGen_1235_;
v___y_1196_ = v___x_1243_;
v___y_1197_ = v_ngen_1234_;
v___y_1198_ = v_traceState_1236_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v_recordedDeps_1237_;
v___y_1201_ = v_snapshotTasks_1240_;
v___y_1202_ = v_nextMacroScope_1233_;
v___y_1203_ = v_messages_1238_;
v___y_1204_ = v_infoState_1239_;
v___y_1205_ = v___x_1246_;
goto v___jp_1194_;
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v_entry_1214_, 1);
lean_dec(v_hint_1190_);
lean_dec(v_mod_1188_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
v___jp_1194_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1);
v___x_1207_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1205_);
lean_ctor_set(v___x_1207_, 1, v___y_1202_);
lean_ctor_set(v___x_1207_, 2, v___y_1197_);
lean_ctor_set(v___x_1207_, 3, v___y_1195_);
lean_ctor_set(v___x_1207_, 4, v___y_1198_);
lean_ctor_set(v___x_1207_, 5, v___x_1206_);
lean_ctor_set(v___x_1207_, 6, v___y_1200_);
lean_ctor_set(v___x_1207_, 7, v___y_1203_);
lean_ctor_set(v___x_1207_, 8, v___y_1204_);
lean_ctor_set(v___x_1207_, 9, v___y_1201_);
v___x_1208_ = lean_st_ref_put(v___y_1199_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___y_1196_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1282_, lean_object* v_isMeta_1283_, lean_object* v_hint_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v_isMeta_boxed_1288_; lean_object* v_res_1289_; 
v_isMeta_boxed_1288_ = lean_unbox(v_isMeta_1283_);
v_res_1289_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1282_, v_isMeta_boxed_1288_, v_hint_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1290_, lean_object* v_declName_1291_, lean_object* v_as_1292_, size_t v_sz_1293_, size_t v_i_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_usize_dec_lt(v_i_1294_, v_sz_1293_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec(v_declName_1291_);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_b_1295_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v_modules_1302_; lean_object* v___x_1303_; lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v_toImport_1306_; lean_object* v_module_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1301_ = l_Lean_Environment_header(v___x_1290_);
v_modules_1302_ = lean_ctor_get(v___x_1301_, 3);
lean_inc_ref(v_modules_1302_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1304_ = lean_array_uget_borrowed(v_as_1292_, v_i_1294_);
v___x_1305_ = lean_array_get(v___x_1303_, v_modules_1302_, v_a_1304_);
lean_dec_ref(v_modules_1302_);
v_toImport_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_toImport_1306_);
lean_dec(v___x_1305_);
v_module_1307_ = lean_ctor_get(v_toImport_1306_, 0);
lean_inc(v_module_1307_);
lean_dec_ref(v_toImport_1306_);
v___x_1308_ = lean_box(0);
v___x_1309_ = 0;
lean_inc(v_declName_1291_);
v___x_1310_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1307_, v___x_1309_, v_declName_1291_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1310_) == 0)
{
size_t v___x_1311_; size_t v___x_1312_; 
lean_dec_ref_known(v___x_1310_, 1);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1294_, v___x_1311_);
v_i_1294_ = v___x_1312_;
v_b_1295_ = v___x_1308_;
goto _start;
}
else
{
lean_dec(v_declName_1291_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1314_, lean_object* v_declName_1315_, lean_object* v_as_1316_, lean_object* v_sz_1317_, lean_object* v_i_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1314_, v_declName_1315_, v_as_1316_, v_sz_boxed_1323_, v_i_boxed_1324_, v_b_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_as_1316_);
lean_dec_ref(v___x_1314_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1326_, lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
else
{
lean_object* v_key_1329_; lean_object* v_value_1330_; lean_object* v_tail_1331_; uint8_t v___x_1332_; 
v_key_1329_ = lean_ctor_get(v_x_1327_, 0);
v_value_1330_ = lean_ctor_get(v_x_1327_, 1);
v_tail_1331_ = lean_ctor_get(v_x_1327_, 2);
v___x_1332_ = lean_name_eq(v_key_1329_, v_a_1326_);
if (v___x_1332_ == 0)
{
v_x_1327_ = v_tail_1331_;
goto _start;
}
else
{
lean_object* v___x_1334_; 
lean_inc(v_value_1330_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_value_1330_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1335_, v_x_1336_);
lean_dec(v_x_1336_);
lean_dec(v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_buckets_1340_; lean_object* v___x_1341_; uint64_t v___y_1343_; 
v_buckets_1340_ = lean_ctor_get(v_m_1338_, 1);
v___x_1341_ = lean_array_get_size(v_buckets_1340_);
if (lean_obj_tag(v_a_1339_) == 0)
{
uint64_t v___x_1357_; 
v___x_1357_ = 1723ULL;
v___y_1343_ = v___x_1357_;
goto v___jp_1342_;
}
else
{
uint64_t v_hash_1358_; 
v_hash_1358_ = lean_ctor_get_uint64(v_a_1339_, sizeof(void*)*2);
v___y_1343_ = v_hash_1358_;
goto v___jp_1342_;
}
v___jp_1342_:
{
uint64_t v___x_1344_; uint64_t v___x_1345_; uint64_t v_fold_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1344_ = 32ULL;
v___x_1345_ = lean_uint64_shift_right(v___y_1343_, v___x_1344_);
v_fold_1346_ = lean_uint64_xor(v___y_1343_, v___x_1345_);
v___x_1347_ = 16ULL;
v___x_1348_ = lean_uint64_shift_right(v_fold_1346_, v___x_1347_);
v___x_1349_ = lean_uint64_xor(v_fold_1346_, v___x_1348_);
v___x_1350_ = lean_uint64_to_usize(v___x_1349_);
v___x_1351_ = lean_usize_of_nat(v___x_1341_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_sub(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_usize_land(v___x_1350_, v___x_1353_);
v___x_1355_ = lean_array_uget_borrowed(v_buckets_1340_, v___x_1354_);
v___x_1356_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1339_, v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_m_1359_);
return v_res_1361_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1365_, uint8_t v_isMeta_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_env_1375_; lean_object* v___y_1377_; lean_object* v___x_1390_; 
v___x_1370_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0);
v___x_1371_ = lean_st_ref_get(v___y_1368_);
v_env_1375_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1371_);
v___x_1390_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1375_, v_declName_1365_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_dec_ref(v_env_1375_);
lean_dec(v_declName_1365_);
goto v___jp_1372_;
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1392_; lean_object* v_modules_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = l_Lean_Environment_header(v_env_1375_);
v_modules_1393_ = lean_ctor_get(v___x_1392_, 3);
lean_inc_ref(v_modules_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = lean_array_get_size(v_modules_1393_);
v___x_1395_ = lean_nat_dec_lt(v_val_1391_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec_ref(v_modules_1393_);
lean_dec(v_val_1391_);
lean_dec_ref(v_env_1375_);
lean_dec(v_declName_1365_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___y_1399_; 
v___x_1396_ = lean_array_fget(v_modules_1393_, v_val_1391_);
lean_dec(v_val_1391_);
lean_dec_ref(v_modules_1393_);
v___x_1397_ = lean_st_ref_get(v___y_1368_);
if (v_isMeta_1366_ == 0)
{
lean_dec(v___x_1397_);
v___y_1399_ = v_isMeta_1366_;
goto v___jp_1398_;
}
else
{
lean_object* v_env_1410_; uint8_t v___x_1411_; 
v_env_1410_ = lean_ctor_get(v___x_1397_, 0);
lean_inc_ref(v_env_1410_);
lean_dec(v___x_1397_);
lean_inc(v_declName_1365_);
v___x_1411_ = l_Lean_isMarkedMeta(v_env_1410_, v_declName_1365_);
if (v___x_1411_ == 0)
{
v___y_1399_ = v_isMeta_1366_;
goto v___jp_1398_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = 0;
v___y_1399_ = v___x_1412_;
goto v___jp_1398_;
}
}
v___jp_1398_:
{
lean_object* v_toImport_1400_; lean_object* v_module_1401_; lean_object* v___x_1402_; 
v_toImport_1400_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_toImport_1400_);
lean_dec(v___x_1396_);
v_module_1401_ = lean_ctor_get(v_toImport_1400_, 0);
lean_inc(v_module_1401_);
lean_dec_ref(v_toImport_1400_);
lean_inc(v_declName_1365_);
v___x_1402_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1401_, v___y_1399_, v_declName_1365_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref_known(v___x_1402_, 1);
v___x_1403_ = l_Lean_indirectModUseExt;
v___x_1404_ = lean_box(1);
v___x_1405_ = lean_box(0);
lean_inc_ref(v_env_1375_);
v___x_1406_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1370_, v___x_1403_, v_env_1375_, v___x_1404_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1406_, v_declName_1365_);
lean_dec(v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___y_1377_ = v___x_1408_;
goto v___jp_1376_;
}
else
{
lean_object* v_val_1409_; 
v_val_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1407_, 1);
v___y_1377_ = v_val_1409_;
goto v___jp_1376_;
}
}
else
{
lean_dec_ref(v_env_1375_);
lean_dec(v_declName_1365_);
return v___x_1402_;
}
}
}
}
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v_sz_1379_ = lean_array_size(v___y_1377_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1375_, v_declName_1365_, v___y_1377_, v_sz_1379_, v___x_1380_, v___x_1378_, v___y_1367_, v___y_1368_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_env_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1389_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1378_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1378_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1413_, lean_object* v_isMeta_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_isMeta_boxed_1418_; lean_object* v_res_1419_; 
v_isMeta_boxed_1418_ = lean_unbox(v_isMeta_1414_);
v_res_1419_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1413_, v_isMeta_boxed_1418_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1420_, uint8_t v_x_1421_, lean_object* v_stx_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
lean_inc(v_stx_1422_);
v___x_1426_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1420_, v_stx_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1479_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1479_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1479_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v_env_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1431_ = lean_st_ref_get(v___y_1424_);
v_env_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc_ref(v_env_1432_);
lean_dec(v___x_1431_);
v___x_1433_ = 1;
lean_inc(v_a_1427_);
v___x_1434_ = l_Lean_Environment_contains(v_env_1432_, v_a_1427_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_stx_1422_);
if (v_isShared_1430_ == 0)
{
v___x_1436_ = v___x_1429_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1427_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
else
{
uint8_t v___x_1438_; lean_object* v___x_1439_; 
lean_del_object(v___x_1429_);
v___x_1438_ = 0;
lean_inc(v_a_1427_);
v___x_1439_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1427_, v___x_1438_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1470_);
v___x_1441_ = v___x_1439_;
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1439_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v_infoState_1444_; uint8_t v_enabled_1445_; 
v___x_1443_ = lean_st_ref_get(v___y_1424_);
v_infoState_1444_ = lean_ctor_get(v___x_1443_, 8);
lean_inc_ref(v_infoState_1444_);
lean_dec(v___x_1443_);
v_enabled_1445_ = lean_ctor_get_uint8(v_infoState_1444_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1444_);
if (v_enabled_1445_ == 0)
{
lean_object* v___x_1447_; 
lean_dec(v_stx_1422_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v_a_1427_);
v___x_1447_ = v___x_1441_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1427_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_del_object(v___x_1441_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = l_Lean_Syntax_getArg(v_stx_1422_, v___x_1449_);
lean_dec(v_stx_1422_);
v___x_1451_ = lean_box(0);
lean_inc(v_a_1427_);
v___x_1452_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1450_, v_a_1427_, v___x_1451_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1452_, 0);
lean_dec(v_unused_1460_);
v___x_1454_ = v___x_1452_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___x_1452_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_a_1427_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1427_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1427_);
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1427_);
lean_dec(v_stx_1422_);
v_a_1471_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1439_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1439_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1422_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1480_, lean_object* v_x_1481_, lean_object* v_stx_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v_x_7329__boxed_1486_; lean_object* v_res_1487_; 
v_x_7329__boxed_1486_ = lean_unbox(v_x_1481_);
v_res_1487_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1480_, v_x_7329__boxed_1486_, v_stx_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1490_, lean_object* v_attrName_1491_, lean_object* v_parserNamespace_1492_, lean_object* v_typeName_1493_, lean_object* v_kind_1494_, lean_object* v_attrDeclName_1495_){
_start:
{
lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___f_1497_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1498_, 0, v_parserNamespace_1492_);
v___x_1499_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1500_ = lean_string_append(v_kind_1494_, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1501_, 0, v_attrBuiltinName_1490_);
lean_ctor_set(v___x_1501_, 1, v_attrName_1491_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
lean_ctor_set(v___x_1501_, 3, v_typeName_1493_);
lean_ctor_set(v___x_1501_, 4, v___f_1498_);
lean_ctor_set(v___x_1501_, 5, v___f_1497_);
v___x_1502_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1501_, v_attrDeclName_1495_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1503_, lean_object* v_attrName_1504_, lean_object* v_parserNamespace_1505_, lean_object* v_typeName_1506_, lean_object* v_kind_1507_, lean_object* v_attrDeclName_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1503_, v_attrName_1504_, v_parserNamespace_1505_, v_typeName_1506_, v_kind_1507_, v_attrDeclName_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1511_, lean_object* v_attrBuiltinName_1512_, lean_object* v_attrName_1513_, lean_object* v_parserNamespace_1514_, lean_object* v_typeName_1515_, lean_object* v_kind_1516_, lean_object* v_attrDeclName_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1512_, v_attrName_1513_, v_parserNamespace_1514_, v_typeName_1515_, v_kind_1516_, v_attrDeclName_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1520_, lean_object* v_attrBuiltinName_1521_, lean_object* v_attrName_1522_, lean_object* v_parserNamespace_1523_, lean_object* v_typeName_1524_, lean_object* v_kind_1525_, lean_object* v_attrDeclName_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1520_, v_attrBuiltinName_1521_, v_attrName_1522_, v_parserNamespace_1523_, v_typeName_1524_, v_kind_1525_, v_attrDeclName_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1529_, lean_object* v_m_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1530_, v_a_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1533_, lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1533_, v_m_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_m_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1537_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
return v_res_1546_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1548_, v_x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1551_, v_x_1552_, v_x_1553_);
lean_dec_ref(v_x_1553_);
lean_dec_ref(v_x_1552_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1556_, lean_object* v_a_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1557_, v_x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1560_, lean_object* v_a_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1560_, v_a_1561_, v_x_1562_);
lean_dec(v_x_1562_);
lean_dec(v_a_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, size_t v_x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v___x_1568_; 
v___x_1568_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1565_, v_x_1566_, v_x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
size_t v_x_7499__boxed_1573_; uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_x_7499__boxed_1573_ = lean_unbox_usize(v_x_1571_);
lean_dec(v_x_1571_);
v_res_1574_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1569_, v_x_1570_, v_x_7499__boxed_1573_, v_x_1572_);
lean_dec_ref(v_x_1572_);
lean_dec_ref(v_x_1570_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1576_, lean_object* v_constName_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1577_, v___y_1578_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_constName_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1582_, v_constName_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1588_, lean_object* v_keys_1589_, lean_object* v_vals_1590_, lean_object* v_heq_1591_, lean_object* v_i_1592_, lean_object* v_k_1593_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1589_, v_i_1592_, v_k_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_keys_1596_, lean_object* v_vals_1597_, lean_object* v_heq_1598_, lean_object* v_i_1599_, lean_object* v_k_1600_){
_start:
{
uint8_t v_res_1601_; lean_object* v_r_1602_; 
v_res_1601_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1595_, v_keys_1596_, v_vals_1597_, v_heq_1598_, v_i_1599_, v_k_1600_);
lean_dec_ref(v_k_1600_);
lean_dec_ref(v_vals_1597_);
lean_dec_ref(v_keys_1596_);
v_r_1602_ = lean_box(v_res_1601_);
return v_r_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1603_, lean_object* v_ref_1604_, lean_object* v_constName_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1604_, v_constName_1605_, v___y_1606_, v___y_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_ref_1611_, lean_object* v_constName_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1610_, v_ref_1611_, v_constName_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v_ref_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1617_, lean_object* v_ref_1618_, lean_object* v_msg_1619_, lean_object* v_declHint_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1618_, v_msg_1619_, v_declHint_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_ref_1626_, lean_object* v_msg_1627_, lean_object* v_declHint_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1625_, v_ref_1626_, v_msg_1627_, v_declHint_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v_ref_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1633_, lean_object* v_declHint_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1633_, v_declHint_1634_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1639_, lean_object* v_declHint_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1639_, v_declHint_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1645_, lean_object* v_ref_1646_, lean_object* v_msg_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1646_, v_msg_1647_, v___y_1648_, v___y_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1652_, lean_object* v_ref_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1652_, v_ref_1653_, v_msg_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v_ref_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1671_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1672_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1673_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1674_ = lean_box(0);
v___x_1675_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1676_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1671_, v___x_1673_, v___x_1674_, v___x_1675_, v___x_1672_, v_ref_1669_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1687_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1694_ = l_Lean_addBuiltinDocString(v___x_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1724_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1725_ = l_Lean_addBuiltinDeclarationRanges(v___x_1723_, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1728_, lean_object* v_a_1729_, lean_object* v_____r_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_declName_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1744_; 
v_declName_1733_ = lean_ctor_get(v_toOLeanEntry_1728_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_toOLeanEntry_1728_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_toOLeanEntry_1728_, 0);
lean_dec(v_unused_1745_);
v___x_1735_ = v_toOLeanEntry_1728_;
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_declName_1733_);
lean_dec(v_toOLeanEntry_1728_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_a_1729_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v___x_1737_);
lean_ctor_set(v___x_1735_, 0, v_declName_1733_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_declName_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___y_1732_);
return v___x_1742_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1746_, lean_object* v_a_1747_, lean_object* v_____r_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1746_, v_a_1747_, v_____r_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1755_, lean_object* v_as_x27_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
if (lean_obj_tag(v_as_x27_1756_) == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_stx_1755_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_b_1757_);
lean_ctor_set(v___x_1760_, 1, v___y_1759_);
return v___x_1760_;
}
else
{
lean_object* v_head_1761_; lean_object* v_tail_1762_; lean_object* v_toOLeanEntry_1763_; uint8_t v_isBuiltin_1764_; lean_object* v_value_1765_; lean_object* v_macroScope_1766_; lean_object* v_traceMsgs_1767_; lean_object* v_expandedMacroDecls_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_b_1757_);
v_head_1761_ = lean_ctor_get(v_as_x27_1756_, 0);
v_tail_1762_ = lean_ctor_get(v_as_x27_1756_, 1);
v_toOLeanEntry_1763_ = lean_ctor_get(v_head_1761_, 0);
v_isBuiltin_1764_ = lean_ctor_get_uint8(v_head_1761_, sizeof(void*)*2);
v_value_1765_ = lean_ctor_get(v_head_1761_, 1);
v_macroScope_1766_ = lean_ctor_get(v___y_1759_, 0);
v_traceMsgs_1767_ = lean_ctor_get(v___y_1759_, 1);
v_expandedMacroDecls_1768_ = lean_ctor_get(v___y_1759_, 2);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___y_1759_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1770_ = v___y_1759_;
v_isShared_1771_ = v_isSharedCheck_1833_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_expandedMacroDecls_1768_);
lean_inc(v_traceMsgs_1767_);
lean_inc(v_macroScope_1766_);
lean_dec(v___y_1759_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1833_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_methods_1772_; lean_object* v_quotContext_1773_; lean_object* v_currRecDepth_1774_; lean_object* v_maxRecDepth_1775_; lean_object* v_ref_1776_; lean_object* v___x_1777_; lean_object* v_a_1779_; lean_object* v_a_1780_; lean_object* v___x_1784_; lean_object* v_a_1786_; lean_object* v_a_1787_; lean_object* v___y_1794_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v_methods_1772_ = lean_ctor_get(v___y_1758_, 0);
v_quotContext_1773_ = lean_ctor_get(v___y_1758_, 1);
v_currRecDepth_1774_ = lean_ctor_get(v___y_1758_, 3);
v_maxRecDepth_1775_ = lean_ctor_get(v___y_1758_, 4);
v_ref_1776_ = lean_ctor_get(v___y_1758_, 5);
v___x_1777_ = lean_box(0);
v___x_1784_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_nat_add(v_macroScope_1766_, v___x_1800_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1801_);
v___x_1803_ = v___x_1770_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_traceMsgs_1767_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_expandedMacroDecls_1768_);
v___x_1803_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1802_;
}
v___jp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_a_1779_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1777_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1780_);
return v___x_1783_;
}
v___jp_1785_:
{
if (lean_obj_tag(v_a_1786_) == 1)
{
v_as_x27_1756_ = v_tail_1762_;
v_b_1757_ = v___x_1784_;
v___y_1759_ = v_a_1787_;
goto _start;
}
else
{
lean_object* v_declName_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v_stx_1755_);
v_declName_1789_ = lean_ctor_get(v_toOLeanEntry_1763_, 1);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1786_);
lean_inc(v_declName_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_declName_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
v_a_1779_ = v___x_1792_;
v_a_1780_ = v_a_1787_;
goto v___jp_1778_;
}
}
v___jp_1793_:
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___y_1794_, 0);
if (lean_obj_tag(v_a_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_a_1797_; 
lean_inc_ref(v_a_1795_);
lean_dec(v_stx_1755_);
v_a_1796_ = lean_ctor_get(v___y_1794_, 1);
lean_inc(v_a_1796_);
lean_dec_ref(v___y_1794_);
v_a_1797_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_a_1795_, 1);
v_a_1779_ = v_a_1797_;
v_a_1780_ = v_a_1796_;
goto v___jp_1778_;
}
else
{
lean_object* v_a_1798_; 
v_a_1798_ = lean_ctor_get(v___y_1794_, 1);
lean_inc(v_a_1798_);
lean_dec_ref(v___y_1794_);
v_as_x27_1756_ = v_tail_1762_;
v_b_1757_ = v___x_1784_;
v___y_1759_ = v_a_1798_;
goto _start;
}
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_inc(v_ref_1776_);
lean_inc(v_maxRecDepth_1775_);
lean_inc(v_currRecDepth_1774_);
lean_inc(v_quotContext_1773_);
lean_inc(v_methods_1772_);
v___x_1804_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1804_, 0, v_methods_1772_);
lean_ctor_set(v___x_1804_, 1, v_quotContext_1773_);
lean_ctor_set(v___x_1804_, 2, v_macroScope_1766_);
lean_ctor_set(v___x_1804_, 3, v_currRecDepth_1774_);
lean_ctor_set(v___x_1804_, 4, v_maxRecDepth_1775_);
lean_ctor_set(v___x_1804_, 5, v_ref_1776_);
lean_inc(v_value_1765_);
lean_inc(v_stx_1755_);
v___x_1805_ = lean_apply_3(v_value_1765_, v_stx_1755_, v___x_1804_, v___x_1803_);
if (lean_obj_tag(v___x_1805_) == 0)
{
if (v_isBuiltin_1764_ == 0)
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1826_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 1);
v_a_1807_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1809_ = v___x_1805_;
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1806_);
lean_inc(v_a_1807_);
lean_dec(v___x_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_macroScope_1811_; lean_object* v_traceMsgs_1812_; lean_object* v_expandedMacroDecls_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_macroScope_1811_ = lean_ctor_get(v_a_1806_, 0);
v_traceMsgs_1812_ = lean_ctor_get(v_a_1806_, 1);
v_expandedMacroDecls_1813_ = lean_ctor_get(v_a_1806_, 2);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1806_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v_a_1806_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_expandedMacroDecls_1813_);
lean_inc(v_traceMsgs_1812_);
lean_inc(v_macroScope_1811_);
lean_dec(v_a_1806_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_declName_1817_; lean_object* v___x_1819_; 
v_declName_1817_ = lean_ctor_get(v_toOLeanEntry_1763_, 1);
lean_inc(v_declName_1817_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 1, v_expandedMacroDecls_1813_);
lean_ctor_set(v___x_1809_, 0, v_declName_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_declName_1817_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_expandedMacroDecls_1813_);
v___x_1819_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 2, v___x_1819_);
v___x_1821_ = v___x_1815_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_macroScope_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_traceMsgs_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
lean_inc_ref(v_toOLeanEntry_1763_);
v___x_1822_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1763_, v_a_1807_, v___x_1777_, v___y_1758_, v___x_1821_);
v___y_1794_ = v___x_1822_;
goto v___jp_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v_a_1828_; lean_object* v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1827_);
v_a_1828_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1805_, 2);
lean_inc_ref(v_toOLeanEntry_1763_);
v___x_1829_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1763_, v_a_1827_, v___x_1777_, v___y_1758_, v_a_1828_);
v___y_1794_ = v___x_1829_;
goto v___jp_1793_;
}
}
else
{
lean_object* v_a_1830_; lean_object* v_a_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1830_);
v_a_1831_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1805_, 2);
v_a_1786_ = v_a_1830_;
v_a_1787_ = v_a_1831_;
goto v___jp_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1834_, v_as_x27_1835_, v_b_1836_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v_as_x27_1835_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1840_, lean_object* v_stx_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v_fst_1851_; 
v___x_1844_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1841_);
v___x_1845_ = l_Lean_Syntax_getKind(v_stx_1841_);
v___x_1846_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1844_, v_env_1840_, v___x_1845_);
lean_dec(v___x_1845_);
v___x_1847_ = lean_box(0);
v___x_1848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1849_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1841_, v___x_1846_, v___x_1848_, v_a_1842_, v_a_1843_);
lean_dec(v___x_1846_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_fst_1851_ = lean_ctor_get(v_a_1850_, 0);
if (lean_obj_tag(v_fst_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1849_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1860_);
v___x_1854_ = v___x_1849_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1849_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1847_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
lean_inc_ref(v_fst_1851_);
v_a_1861_ = lean_ctor_get(v___x_1849_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1870_);
v___x_1863_ = v___x_1849_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1849_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_val_1865_; lean_object* v___x_1867_; 
v_val_1865_ = lean_ctor_get(v_fst_1851_, 0);
lean_inc(v_val_1865_);
lean_dec_ref_known(v_fst_1851_, 1);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_val_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_val_1865_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_a_1861_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1871_, lean_object* v_stx_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1871_, v_stx_1872_, v_a_1873_, v_a_1874_);
lean_dec_ref(v_a_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1876_, lean_object* v_as_1877_, lean_object* v_as_x27_1878_, lean_object* v_b_1879_, lean_object* v_a_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1876_, v_as_x27_1878_, v_b_1879_, v___y_1881_, v___y_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1884_, lean_object* v_as_1885_, lean_object* v_as_x27_1886_, lean_object* v_b_1887_, lean_object* v_a_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1884_, v_as_1885_, v_as_x27_1886_, v_b_1887_, v_a_1888_, v___y_1889_, v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v_as_x27_1886_);
lean_dec(v_as_1885_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1892_, lean_object* v_inst_1893_, lean_object* v_s_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_apply_1(v_setNextMacroScope_1892_, v_s_1894_);
v___x_1896_ = lean_apply_2(v_inst_1893_, lean_box(0), v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_){
_start:
{
lean_object* v_getNextMacroScope_1900_; lean_object* v_setNextMacroScope_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1910_; 
v_getNextMacroScope_1900_ = lean_ctor_get(v_inst_1899_, 1);
v_setNextMacroScope_1901_ = lean_ctor_get(v_inst_1899_, 2);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_inst_1899_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v_inst_1899_, 0);
lean_dec(v_unused_1911_);
v___x_1903_ = v_inst_1899_;
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_setNextMacroScope_1901_);
lean_inc(v_getNextMacroScope_1900_);
lean_dec(v_inst_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_inc(v_inst_1897_);
v___f_1905_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1905_, 0, v_setNextMacroScope_1901_);
lean_closure_set(v___f_1905_, 1, v_inst_1897_);
v___x_1906_ = lean_apply_2(v_inst_1897_, lean_box(0), v_getNextMacroScope_1900_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 2, v___f_1905_);
lean_ctor_set(v___x_1903_, 1, v___x_1906_);
lean_ctor_set(v___x_1903_, 0, v_inst_1898_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_inst_1898_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___f_1905_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1912_, lean_object* v_n_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_){
_start:
{
lean_object* v_getNextMacroScope_1917_; lean_object* v_setNextMacroScope_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v_getNextMacroScope_1917_ = lean_ctor_get(v_inst_1916_, 1);
v_setNextMacroScope_1918_ = lean_ctor_get(v_inst_1916_, 2);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_inst_1916_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_inst_1916_, 0);
lean_dec(v_unused_1928_);
v___x_1920_ = v_inst_1916_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_setNextMacroScope_1918_);
lean_inc(v_getNextMacroScope_1917_);
lean_dec(v_inst_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
lean_inc(v_inst_1914_);
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1922_, 0, v_setNextMacroScope_1918_);
lean_closure_set(v___f_1922_, 1, v_inst_1914_);
v___x_1923_ = lean_apply_2(v_inst_1914_, lean_box(0), v_getNextMacroScope_1917_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 2, v___f_1922_);
lean_ctor_set(v___x_1920_, 1, v___x_1923_);
lean_ctor_set(v___x_1920_, 0, v_inst_1915_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_inst_1915_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v___f_1922_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0(lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_nextMacroScope_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_nextMacroScope_1933_ = lean_ctor_get(v___x_1932_, 1);
lean_inc(v_nextMacroScope_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_nextMacroScope_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0___boxed(lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0(v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1(lean_object* v_next_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_env_1944_; lean_object* v_ngen_1945_; lean_object* v_auxDeclNGen_1946_; lean_object* v_traceState_1947_; lean_object* v_cache_1948_; lean_object* v_recordedDeps_1949_; lean_object* v_messages_1950_; lean_object* v_infoState_1951_; lean_object* v_snapshotTasks_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1962_; 
v___x_1943_ = lean_st_ref_take(v___y_1941_);
v_env_1944_ = lean_ctor_get(v___x_1943_, 0);
v_ngen_1945_ = lean_ctor_get(v___x_1943_, 2);
v_auxDeclNGen_1946_ = lean_ctor_get(v___x_1943_, 3);
v_traceState_1947_ = lean_ctor_get(v___x_1943_, 4);
v_cache_1948_ = lean_ctor_get(v___x_1943_, 5);
v_recordedDeps_1949_ = lean_ctor_get(v___x_1943_, 6);
v_messages_1950_ = lean_ctor_get(v___x_1943_, 7);
v_infoState_1951_ = lean_ctor_get(v___x_1943_, 8);
v_snapshotTasks_1952_ = lean_ctor_get(v___x_1943_, 9);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1943_, 1);
lean_dec(v_unused_1963_);
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snapshotTasks_1952_);
lean_inc(v_infoState_1951_);
lean_inc(v_messages_1950_);
lean_inc(v_recordedDeps_1949_);
lean_inc(v_cache_1948_);
lean_inc(v_traceState_1947_);
lean_inc(v_auxDeclNGen_1946_);
lean_inc(v_ngen_1945_);
lean_inc(v_env_1944_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_box(0);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_next_1939_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_env_1944_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_next_1939_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_ngen_1945_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_auxDeclNGen_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_traceState_1947_);
lean_ctor_set(v_reuseFailAlloc_1961_, 5, v_cache_1948_);
lean_ctor_set(v_reuseFailAlloc_1961_, 6, v_recordedDeps_1949_);
lean_ctor_set(v_reuseFailAlloc_1961_, 7, v_messages_1950_);
lean_ctor_set(v_reuseFailAlloc_1961_, 8, v_infoState_1951_);
lean_ctor_set(v_reuseFailAlloc_1961_, 9, v_snapshotTasks_1952_);
v___x_1958_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_st_ref_put(v___y_1941_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1956_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1___boxed(lean_object* v_next_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1(v_next_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1968_;
}
}
static lean_object* _init_l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2(void){
_start:
{
lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___f_1971_ = ((lean_object*)(l_Lean_Elab_instMonadMacroAdapterCoreM___closed__1));
v___f_1972_ = ((lean_object*)(l_Lean_Elab_instMonadMacroAdapterCoreM___closed__0));
v___x_1973_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___f_1972_);
lean_ctor_set(v___x_1974_, 2, v___f_1971_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Elab_instMonadMacroAdapterCoreM(void){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_obj_once(&l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2, &l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2_once, _init_l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2);
return v___x_1975_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_hasNameCollision___lam__0(lean_object* v_env_1976_, lean_object* v_additionalConstants_1977_, lean_object* v_nm_1978_){
_start:
{
uint8_t v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = 1;
lean_inc(v_nm_1978_);
v___x_1980_ = l_Lean_Environment_contains(v_env_1976_, v_nm_1978_, v___x_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_apply_1(v_additionalConstants_1977_, v_nm_1978_);
v___x_1982_ = lean_unbox(v___x_1981_);
return v___x_1982_;
}
else
{
lean_dec(v_nm_1978_);
lean_dec_ref(v_additionalConstants_1977_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_hasNameCollision___lam__0___boxed(lean_object* v_env_1983_, lean_object* v_additionalConstants_1984_, lean_object* v_nm_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = l_Lean_Elab_hasNameCollision___lam__0(v_env_1983_, v_additionalConstants_1984_, v_nm_1985_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_hasNameCollision(lean_object* v_env_1988_, lean_object* v_declName_1989_, lean_object* v_additionalConstants_1990_){
_start:
{
uint8_t v___x_1991_; lean_object* v_env_1992_; uint8_t v___x_1993_; 
v___x_1991_ = 0;
v_env_1992_ = l_Lean_Environment_setExporting(v_env_1988_, v___x_1991_);
lean_inc(v_declName_1989_);
lean_inc_ref(v_additionalConstants_1990_);
lean_inc_ref(v_env_1992_);
v___x_1993_ = l_Lean_Elab_hasNameCollision___lam__0(v_env_1992_, v_additionalConstants_1990_, v_declName_1989_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_inc(v_declName_1989_);
v___x_1994_ = l_Lean_mkPrivateName(v_env_1992_, v_declName_1989_);
lean_inc_ref(v_additionalConstants_1990_);
lean_inc_ref(v_env_1992_);
v___x_1995_ = l_Lean_Elab_hasNameCollision___lam__0(v_env_1992_, v_additionalConstants_1990_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_privateToUserName_x3f(v_declName_1989_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref(v_env_1992_);
lean_dec_ref(v_additionalConstants_1990_);
return v___x_1995_;
}
else
{
lean_object* v_val_1997_; uint8_t v___x_1998_; 
v_val_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Elab_hasNameCollision___lam__0(v_env_1992_, v_additionalConstants_1990_, v_val_1997_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v_env_1992_);
lean_dec_ref(v_additionalConstants_1990_);
lean_dec(v_declName_1989_);
return v___x_1995_;
}
}
else
{
lean_dec_ref(v_env_1992_);
lean_dec_ref(v_additionalConstants_1990_);
lean_dec(v_declName_1989_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_hasNameCollision___boxed(lean_object* v_env_1999_, lean_object* v_declName_2000_, lean_object* v_additionalConstants_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l_Lean_Elab_hasNameCollision(v_env_1999_, v_declName_2000_, v_additionalConstants_2001_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_2004_, lean_object* v_fst_2005_, lean_object* v_____do__lift_2006_, lean_object* v_____do__lift_2007_){
_start:
{
uint8_t v_hasTrace_2008_; 
v_hasTrace_2008_ = lean_ctor_get_uint8(v_____do__lift_2007_, sizeof(void*)*1);
if (v_hasTrace_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_fst_2005_);
v___x_2009_ = lean_box(v_hasTrace_2008_);
v___x_2010_ = lean_apply_2(v_toPure_2004_, lean_box(0), v___x_2009_);
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_2012_ = l_Lean_Name_append(v___x_2011_, v_fst_2005_);
v___x_2013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2006_, v_____do__lift_2007_, v___x_2012_);
lean_dec(v___x_2012_);
v___x_2014_ = lean_box(v___x_2013_);
v___x_2015_ = lean_apply_2(v_toPure_2004_, lean_box(0), v___x_2014_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_2016_, lean_object* v_fst_2017_, lean_object* v_____do__lift_2018_, lean_object* v_____do__lift_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_2016_, v_fst_2017_, v_____do__lift_2018_, v_____do__lift_2019_);
lean_dec_ref(v_____do__lift_2019_);
lean_dec_ref(v_____do__lift_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_inst_2021_, lean_object* v_toPure_2022_, lean_object* v_fst_2023_, lean_object* v_toBind_2024_, lean_object* v_____do__lift_2025_){
_start:
{
lean_object* v_getOptionsUnrestricted_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; 
v_getOptionsUnrestricted_2026_ = lean_ctor_get(v_inst_2021_, 1);
lean_inc(v_getOptionsUnrestricted_2026_);
lean_dec_ref(v_inst_2021_);
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2027_, 0, v_toPure_2022_);
lean_closure_set(v___f_2027_, 1, v_fst_2023_);
lean_closure_set(v___f_2027_, 2, v_____do__lift_2025_);
v___x_2028_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2026_, v___f_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_2029_, lean_object* v_snd_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_toMonadRef_2033_, lean_object* v_inst_2034_, lean_object* v_fst_2035_, uint8_t v_____do__lift_2036_){
_start:
{
if (v_____do__lift_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_fst_2035_);
lean_dec(v_inst_2034_);
lean_dec_ref(v_toMonadRef_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_inst_2031_);
lean_dec_ref(v_snd_2030_);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_apply_2(v_toPure_2029_, lean_box(0), v___x_2037_);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec(v_toPure_2029_);
v___x_2039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_snd_2030_);
v___x_2040_ = l_Lean_MessageData_ofFormat(v___x_2039_);
v___x_2041_ = l_Lean_addTrace___redArg(v_inst_2031_, v_inst_2032_, v_toMonadRef_2033_, v_inst_2034_, v_fst_2035_, v___x_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object* v_toPure_2042_, lean_object* v_snd_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_toMonadRef_2046_, lean_object* v_inst_2047_, lean_object* v_fst_2048_, lean_object* v_____do__lift_2049_){
_start:
{
uint8_t v_____do__lift_1455__boxed_2050_; lean_object* v_res_2051_; 
v_____do__lift_1455__boxed_2050_ = lean_unbox(v_____do__lift_2049_);
v_res_2051_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_toPure_2042_, v_snd_2043_, v_inst_2044_, v_inst_2045_, v_toMonadRef_2046_, v_inst_2047_, v_fst_2048_, v_____do__lift_1455__boxed_2050_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_toPure_2054_, lean_object* v_toBind_2055_, lean_object* v_inst_2056_, lean_object* v_toMonadRef_2057_, lean_object* v_inst_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v_getInheritedTraceOptions_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_fst_2060_ = lean_ctor_get(v_x_2059_, 0);
lean_inc_n(v_fst_2060_, 2);
v_snd_2061_ = lean_ctor_get(v_x_2059_, 1);
lean_inc(v_snd_2061_);
lean_dec_ref(v_x_2059_);
v_getInheritedTraceOptions_2062_ = lean_ctor_get(v_inst_2052_, 2);
lean_inc(v_getInheritedTraceOptions_2062_);
lean_inc_n(v_toBind_2055_, 2);
lean_inc(v_toPure_2054_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2063_, 0, v_inst_2053_);
lean_closure_set(v___f_2063_, 1, v_toPure_2054_);
lean_closure_set(v___f_2063_, 2, v_fst_2060_);
lean_closure_set(v___f_2063_, 3, v_toBind_2055_);
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2064_, 0, v_toPure_2054_);
lean_closure_set(v___f_2064_, 1, v_snd_2061_);
lean_closure_set(v___f_2064_, 2, v_inst_2056_);
lean_closure_set(v___f_2064_, 3, v_inst_2052_);
lean_closure_set(v___f_2064_, 4, v_toMonadRef_2057_);
lean_closure_set(v___f_2064_, 5, v_inst_2058_);
lean_closure_set(v___f_2064_, 6, v_fst_2060_);
v___x_2065_ = lean_apply_4(v_toBind_2055_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2062_, v___f_2063_);
v___x_2066_ = lean_apply_4(v_toBind_2055_, lean_box(0), lean_box(0), v___x_2065_, v___f_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_2067_, lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v_stx_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2067_, v_stx_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
if (lean_obj_tag(v_a_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
v_a_2075_ = lean_ctor_get(v___x_2073_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2073_, 0);
lean_dec(v_unused_2084_);
v___x_2077_ = v___x_2073_;
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2073_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2079_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_a_2075_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2115_; 
v_val_2085_ = lean_ctor_get(v_a_2074_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2087_ = v_a_2074_;
v_isShared_2088_ = v_isSharedCheck_2115_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_dec(v_a_2074_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2115_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_snd_2089_; 
v_snd_2089_ = lean_ctor_get(v_val_2085_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_val_2085_);
if (lean_obj_tag(v_snd_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2100_; 
lean_del_object(v___x_2087_);
v_a_2090_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2073_, 2);
v_a_2091_ = lean_ctor_get(v_snd_2089_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_snd_2089_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2093_ = v_snd_2089_;
v_isShared_2094_ = v_isSharedCheck_2100_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v_snd_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2100_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_1192__overap_2097_; lean_object* v___x_2098_; 
v___x_1192__overap_2097_ = l_liftExcept___redArg(v___x_2068_, v___x_2069_, v___x_2096_);
lean_inc_ref(v___y_2071_);
v___x_2098_ = lean_apply_2(v___x_1192__overap_2097_, v___y_2071_, v_a_2090_);
return v___x_2098_;
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2114_; 
v_a_2101_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2073_, 2);
v_a_2102_ = lean_ctor_get(v_snd_2089_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_snd_2089_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2104_ = v_snd_2089_;
v_isShared_2105_ = v_isSharedCheck_2114_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v_snd_2089_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2114_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v_a_2102_);
v___x_2107_ = v___x_2087_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2109_ = v___x_2104_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_1196__overap_2110_; lean_object* v___x_2111_; 
v___x_1196__overap_2110_ = l_liftExcept___redArg(v___x_2068_, v___x_2069_, v___x_2109_);
lean_inc_ref(v___y_2071_);
v___x_2111_ = lean_apply_2(v___x_1196__overap_2110_, v___y_2071_, v_a_2101_);
return v___x_2111_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
v_a_2116_ = lean_ctor_get(v___x_2073_, 0);
v_a_2117_ = lean_ctor_get(v___x_2073_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2073_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_inc(v_a_2116_);
lean_dec(v___x_2073_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2125_, lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_stx_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2125_, v___x_2126_, v___x_2127_, v_stx_2128_, v___y_2129_, v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2132_, lean_object* v_nm_2133_){
_start:
{
uint8_t v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = 1;
v___x_2135_ = l_Lean_Environment_contains(v_env_2132_, v_nm_2133_, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2136_, lean_object* v_nm_2137_){
_start:
{
uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_res_2138_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2136_, v_nm_2137_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2140_, lean_object* v_declName_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
uint8_t v___x_2144_; lean_object* v_env_2145_; uint8_t v___x_2146_; 
v___x_2144_ = 0;
v_env_2145_ = l_Lean_Environment_setExporting(v_env_2140_, v___x_2144_);
lean_inc(v_declName_2141_);
lean_inc_ref(v_env_2145_);
v___x_2146_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2145_, v_declName_2141_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
lean_inc(v_declName_2141_);
v___x_2147_ = l_Lean_mkPrivateName(v_env_2145_, v_declName_2141_);
lean_inc_ref(v_env_2145_);
v___x_2148_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2145_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_privateToUserName_x3f(v_declName_2141_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_env_2145_);
v___x_2150_ = lean_box(v___x_2148_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___y_2143_);
return v___x_2151_;
}
else
{
lean_object* v_val_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_val_2152_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2153_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2145_, v_val_2152_);
v___x_2154_ = lean_box(v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___y_2143_);
return v___x_2155_;
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_env_2145_);
lean_dec(v_declName_2141_);
v___x_2156_ = lean_box(v___x_2148_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___y_2143_);
return v___x_2157_;
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v_env_2145_);
lean_dec(v_declName_2141_);
v___x_2158_ = lean_box(v___x_2146_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___y_2143_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2160_, lean_object* v_declName_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2160_, v_declName_2161_, v___y_2162_, v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2165_, lean_object* v_currNamespace_2166_, lean_object* v_openDecls_2167_, lean_object* v_n_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = l_Lean_ResolveName_resolveNamespace(v_env_2165_, v_currNamespace_2166_, v_openDecls_2167_, v_n_2168_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___y_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2173_, lean_object* v_currNamespace_2174_, lean_object* v_openDecls_2175_, lean_object* v_n_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2173_, v_currNamespace_2174_, v_openDecls_2175_, v_n_2176_, v___y_2177_, v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_env_2180_, lean_object* v_opts_2181_, lean_object* v_currNamespace_2182_, lean_object* v_openDecls_2183_, lean_object* v_n_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = l_Lean_ResolveName_resolveGlobalName(v_env_2180_, v_opts_2181_, v_currNamespace_2182_, v_openDecls_2183_, v_n_2184_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8___boxed(lean_object* v_env_2189_, lean_object* v_opts_2190_, lean_object* v_currNamespace_2191_, lean_object* v_openDecls_2192_, lean_object* v_n_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Elab_liftMacroM___redArg___lam__8(v_env_2189_, v_opts_2190_, v_currNamespace_2191_, v_openDecls_2192_, v_n_2193_, v___y_2194_, v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v_opts_2190_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_toPure_2197_, lean_object* v_a_2198_, lean_object* v_____r_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_apply_2(v_toPure_2197_, lean_box(0), v_a_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_traceMsgs_2201_, lean_object* v_inst_2202_, lean_object* v___f_2203_, lean_object* v_toBind_2204_, lean_object* v___f_2205_, lean_object* v_____r_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = l_List_reverse___redArg(v_traceMsgs_2201_);
v___x_2208_ = l_List_forM___redArg(v_inst_2202_, v___x_2207_, v___f_2203_);
v___x_2209_ = lean_apply_4(v_toBind_2204_, lean_box(0), lean_box(0), v___x_2208_, v___f_2205_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v_setNextMacroScope_2210_, lean_object* v_macroScope_2211_, lean_object* v_toBind_2212_, lean_object* v___f_2213_, lean_object* v_____s_2214_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_apply_1(v_setNextMacroScope_2210_, v_macroScope_2211_);
v___x_2216_ = lean_apply_4(v_toBind_2212_, lean_box(0), lean_box(0), v___x_2215_, v___f_2213_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v___x_2217_, lean_object* v_toPure_2218_, lean_object* v_____r_2219_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
v___x_2221_ = lean_apply_2(v_toPure_2218_, lean_box(0), v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_toMonadRef_2226_, lean_object* v_inst_2227_, lean_object* v_toBind_2228_, lean_object* v___f_2229_, lean_object* v_a_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = 1;
v___x_2234_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2222_, v_inst_2223_, v_inst_2224_, v_inst_2225_, v_toMonadRef_2226_, v_inst_2227_, v_a_2230_, v___x_2233_);
v___x_2235_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2234_, v___f_2229_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2237_, lean_object* v_____do__lift_2238_, lean_object* v_____do__lift_2239_, lean_object* v_____do__lift_2240_, lean_object* v_____do__lift_2241_, lean_object* v_____do__lift_2242_, lean_object* v_x_2243_, lean_object* v_toPure_2244_, lean_object* v_inst_2245_, lean_object* v___f_2246_, lean_object* v_toBind_2247_, lean_object* v_setNextMacroScope_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_toMonadRef_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_toMonadExceptOf_2255_, lean_object* v_____do__lift_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2257_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2257_, 0, v_methods_2237_);
lean_ctor_set(v___x_2257_, 1, v_____do__lift_2238_);
lean_ctor_set(v___x_2257_, 2, v_____do__lift_2239_);
lean_ctor_set(v___x_2257_, 3, v_____do__lift_2240_);
lean_ctor_set(v___x_2257_, 4, v_____do__lift_2241_);
lean_ctor_set(v___x_2257_, 5, v_____do__lift_2242_);
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2259_, 0, v_____do__lift_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
lean_ctor_set(v___x_2259_, 2, v___x_2258_);
v___x_2260_ = lean_apply_2(v_x_2243_, v___x_2257_, v___x_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v_macroScope_2263_; lean_object* v_traceMsgs_2264_; lean_object* v_expandedMacroDecls_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_toMonadExceptOf_2255_);
lean_dec_ref(v_inst_2254_);
v_a_2261_ = lean_ctor_get(v___x_2260_, 1);
lean_inc(v_a_2261_);
v_a_2262_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2260_, 2);
v_macroScope_2263_ = lean_ctor_get(v_a_2261_, 0);
lean_inc(v_macroScope_2263_);
v_traceMsgs_2264_ = lean_ctor_get(v_a_2261_, 1);
lean_inc(v_traceMsgs_2264_);
v_expandedMacroDecls_2265_ = lean_ctor_get(v_a_2261_, 2);
lean_inc(v_expandedMacroDecls_2265_);
lean_dec(v_a_2261_);
lean_inc(v_toPure_2244_);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_2266_, 0, v_toPure_2244_);
lean_closure_set(v___f_2266_, 1, v_a_2262_);
lean_inc_n(v_toBind_2247_, 3);
lean_inc_ref_n(v_inst_2245_, 2);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 6, 5);
lean_closure_set(v___f_2267_, 0, v_traceMsgs_2264_);
lean_closure_set(v___f_2267_, 1, v_inst_2245_);
lean_closure_set(v___f_2267_, 2, v___f_2246_);
lean_closure_set(v___f_2267_, 3, v_toBind_2247_);
lean_closure_set(v___f_2267_, 4, v___f_2266_);
v___f_2268_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 5, 4);
lean_closure_set(v___f_2268_, 0, v_setNextMacroScope_2248_);
lean_closure_set(v___f_2268_, 1, v_macroScope_2263_);
lean_closure_set(v___f_2268_, 2, v_toBind_2247_);
lean_closure_set(v___f_2268_, 3, v___f_2267_);
v___x_2269_ = lean_box(0);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 3, 2);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
lean_closure_set(v___f_2270_, 1, v_toPure_2244_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13), 11, 8);
lean_closure_set(v___f_2271_, 0, v_inst_2245_);
lean_closure_set(v___f_2271_, 1, v_inst_2249_);
lean_closure_set(v___f_2271_, 2, v_inst_2250_);
lean_closure_set(v___f_2271_, 3, v_inst_2251_);
lean_closure_set(v___f_2271_, 4, v_toMonadRef_2252_);
lean_closure_set(v___f_2271_, 5, v_inst_2253_);
lean_closure_set(v___f_2271_, 6, v_toBind_2247_);
lean_closure_set(v___f_2271_, 7, v___f_2270_);
v___x_2272_ = l_List_forIn_x27_loop___redArg(v_inst_2245_, v___f_2271_, v_expandedMacroDecls_2265_, v___x_2269_);
lean_dec(v_expandedMacroDecls_2265_);
v___x_2273_ = lean_apply_4(v_toBind_2247_, lean_box(0), lean_box(0), v___x_2272_, v___f_2268_);
return v___x_2273_;
}
else
{
lean_object* v_a_2274_; 
lean_dec(v_inst_2253_);
lean_dec_ref(v_toMonadRef_2252_);
lean_dec_ref(v_inst_2251_);
lean_dec_ref(v_inst_2250_);
lean_dec_ref(v_inst_2249_);
lean_dec(v_setNextMacroScope_2248_);
lean_dec(v_toBind_2247_);
lean_dec(v___f_2246_);
lean_dec(v_toPure_2244_);
v_a_2274_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2260_, 2);
if (lean_obj_tag(v_a_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
lean_dec_ref(v_toMonadExceptOf_2255_);
v_a_2275_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_a_2275_);
v_a_2276_ = lean_ctor_get(v_a_2274_, 1);
lean_inc_ref(v_a_2276_);
lean_dec_ref_known(v_a_2274_, 2);
v___x_2277_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__14___closed__0));
v___x_2278_ = lean_string_dec_eq(v_a_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2276_);
v___x_2280_ = l_Lean_MessageData_ofFormat(v___x_2279_);
v___x_2281_ = l_Lean_throwErrorAt___redArg(v_inst_2245_, v_inst_2254_, v_a_2275_, v___x_2280_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; 
lean_dec_ref(v_a_2276_);
lean_dec_ref(v_inst_2245_);
v___x_2282_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2254_, v_a_2275_);
return v___x_2282_;
}
}
else
{
lean_object* v___x_2283_; 
lean_dec_ref(v_inst_2254_);
lean_dec_ref(v_inst_2245_);
v___x_2283_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2255_);
return v___x_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2284_ = _args[0];
lean_object* v_____do__lift_2285_ = _args[1];
lean_object* v_____do__lift_2286_ = _args[2];
lean_object* v_____do__lift_2287_ = _args[3];
lean_object* v_____do__lift_2288_ = _args[4];
lean_object* v_____do__lift_2289_ = _args[5];
lean_object* v_x_2290_ = _args[6];
lean_object* v_toPure_2291_ = _args[7];
lean_object* v_inst_2292_ = _args[8];
lean_object* v___f_2293_ = _args[9];
lean_object* v_toBind_2294_ = _args[10];
lean_object* v_setNextMacroScope_2295_ = _args[11];
lean_object* v_inst_2296_ = _args[12];
lean_object* v_inst_2297_ = _args[13];
lean_object* v_inst_2298_ = _args[14];
lean_object* v_toMonadRef_2299_ = _args[15];
lean_object* v_inst_2300_ = _args[16];
lean_object* v_inst_2301_ = _args[17];
lean_object* v_toMonadExceptOf_2302_ = _args[18];
lean_object* v_____do__lift_2303_ = _args[19];
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2284_, v_____do__lift_2285_, v_____do__lift_2286_, v_____do__lift_2287_, v_____do__lift_2288_, v_____do__lift_2289_, v_x_2290_, v_toPure_2291_, v_inst_2292_, v___f_2293_, v_toBind_2294_, v_setNextMacroScope_2295_, v_inst_2296_, v_inst_2297_, v_inst_2298_, v_toMonadRef_2299_, v_inst_2300_, v_inst_2301_, v_toMonadExceptOf_2302_, v_____do__lift_2303_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2305_, lean_object* v_____do__lift_2306_, lean_object* v_____do__lift_2307_, lean_object* v_____do__lift_2308_, lean_object* v_____do__lift_2309_, lean_object* v_x_2310_, lean_object* v_toPure_2311_, lean_object* v_inst_2312_, lean_object* v___f_2313_, lean_object* v_toBind_2314_, lean_object* v_setNextMacroScope_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_toMonadRef_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_toMonadExceptOf_2322_, lean_object* v_getNextMacroScope_2323_, lean_object* v_____do__lift_2324_){
_start:
{
lean_object* v___f_2325_; lean_object* v___x_2326_; 
lean_inc(v_toBind_2314_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2325_, 0, v_methods_2305_);
lean_closure_set(v___f_2325_, 1, v_____do__lift_2306_);
lean_closure_set(v___f_2325_, 2, v_____do__lift_2307_);
lean_closure_set(v___f_2325_, 3, v_____do__lift_2308_);
lean_closure_set(v___f_2325_, 4, v_____do__lift_2324_);
lean_closure_set(v___f_2325_, 5, v_____do__lift_2309_);
lean_closure_set(v___f_2325_, 6, v_x_2310_);
lean_closure_set(v___f_2325_, 7, v_toPure_2311_);
lean_closure_set(v___f_2325_, 8, v_inst_2312_);
lean_closure_set(v___f_2325_, 9, v___f_2313_);
lean_closure_set(v___f_2325_, 10, v_toBind_2314_);
lean_closure_set(v___f_2325_, 11, v_setNextMacroScope_2315_);
lean_closure_set(v___f_2325_, 12, v_inst_2316_);
lean_closure_set(v___f_2325_, 13, v_inst_2317_);
lean_closure_set(v___f_2325_, 14, v_inst_2318_);
lean_closure_set(v___f_2325_, 15, v_toMonadRef_2319_);
lean_closure_set(v___f_2325_, 16, v_inst_2320_);
lean_closure_set(v___f_2325_, 17, v_inst_2321_);
lean_closure_set(v___f_2325_, 18, v_toMonadExceptOf_2322_);
v___x_2326_ = lean_apply_4(v_toBind_2314_, lean_box(0), lean_box(0), v_getNextMacroScope_2323_, v___f_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2327_ = _args[0];
lean_object* v_____do__lift_2328_ = _args[1];
lean_object* v_____do__lift_2329_ = _args[2];
lean_object* v_____do__lift_2330_ = _args[3];
lean_object* v_____do__lift_2331_ = _args[4];
lean_object* v_x_2332_ = _args[5];
lean_object* v_toPure_2333_ = _args[6];
lean_object* v_inst_2334_ = _args[7];
lean_object* v___f_2335_ = _args[8];
lean_object* v_toBind_2336_ = _args[9];
lean_object* v_setNextMacroScope_2337_ = _args[10];
lean_object* v_inst_2338_ = _args[11];
lean_object* v_inst_2339_ = _args[12];
lean_object* v_inst_2340_ = _args[13];
lean_object* v_toMonadRef_2341_ = _args[14];
lean_object* v_inst_2342_ = _args[15];
lean_object* v_inst_2343_ = _args[16];
lean_object* v_toMonadExceptOf_2344_ = _args[17];
lean_object* v_getNextMacroScope_2345_ = _args[18];
lean_object* v_____do__lift_2346_ = _args[19];
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2327_, v_____do__lift_2328_, v_____do__lift_2329_, v_____do__lift_2330_, v_____do__lift_2331_, v_x_2332_, v_toPure_2333_, v_inst_2334_, v___f_2335_, v_toBind_2336_, v_setNextMacroScope_2337_, v_inst_2338_, v_inst_2339_, v_inst_2340_, v_toMonadRef_2341_, v_inst_2342_, v_inst_2343_, v_toMonadExceptOf_2344_, v_getNextMacroScope_2345_, v_____do__lift_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_methods_2348_, lean_object* v_____do__lift_2349_, lean_object* v_____do__lift_2350_, lean_object* v_____do__lift_2351_, lean_object* v_x_2352_, lean_object* v_toPure_2353_, lean_object* v_inst_2354_, lean_object* v___f_2355_, lean_object* v_toBind_2356_, lean_object* v_setNextMacroScope_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_toMonadRef_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_toMonadExceptOf_2364_, lean_object* v_getNextMacroScope_2365_, lean_object* v_getMaxRecDepth_2366_, lean_object* v_____do__lift_2367_){
_start:
{
lean_object* v___f_2368_; lean_object* v___x_2369_; 
lean_inc(v_toBind_2356_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2368_, 0, v_methods_2348_);
lean_closure_set(v___f_2368_, 1, v_____do__lift_2349_);
lean_closure_set(v___f_2368_, 2, v_____do__lift_2350_);
lean_closure_set(v___f_2368_, 3, v_____do__lift_2367_);
lean_closure_set(v___f_2368_, 4, v_____do__lift_2351_);
lean_closure_set(v___f_2368_, 5, v_x_2352_);
lean_closure_set(v___f_2368_, 6, v_toPure_2353_);
lean_closure_set(v___f_2368_, 7, v_inst_2354_);
lean_closure_set(v___f_2368_, 8, v___f_2355_);
lean_closure_set(v___f_2368_, 9, v_toBind_2356_);
lean_closure_set(v___f_2368_, 10, v_setNextMacroScope_2357_);
lean_closure_set(v___f_2368_, 11, v_inst_2358_);
lean_closure_set(v___f_2368_, 12, v_inst_2359_);
lean_closure_set(v___f_2368_, 13, v_inst_2360_);
lean_closure_set(v___f_2368_, 14, v_toMonadRef_2361_);
lean_closure_set(v___f_2368_, 15, v_inst_2362_);
lean_closure_set(v___f_2368_, 16, v_inst_2363_);
lean_closure_set(v___f_2368_, 17, v_toMonadExceptOf_2364_);
lean_closure_set(v___f_2368_, 18, v_getNextMacroScope_2365_);
v___x_2369_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v_getMaxRecDepth_2366_, v___f_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_methods_2370_ = _args[0];
lean_object* v_____do__lift_2371_ = _args[1];
lean_object* v_____do__lift_2372_ = _args[2];
lean_object* v_____do__lift_2373_ = _args[3];
lean_object* v_x_2374_ = _args[4];
lean_object* v_toPure_2375_ = _args[5];
lean_object* v_inst_2376_ = _args[6];
lean_object* v___f_2377_ = _args[7];
lean_object* v_toBind_2378_ = _args[8];
lean_object* v_setNextMacroScope_2379_ = _args[9];
lean_object* v_inst_2380_ = _args[10];
lean_object* v_inst_2381_ = _args[11];
lean_object* v_inst_2382_ = _args[12];
lean_object* v_toMonadRef_2383_ = _args[13];
lean_object* v_inst_2384_ = _args[14];
lean_object* v_inst_2385_ = _args[15];
lean_object* v_toMonadExceptOf_2386_ = _args[16];
lean_object* v_getNextMacroScope_2387_ = _args[17];
lean_object* v_getMaxRecDepth_2388_ = _args[18];
lean_object* v_____do__lift_2389_ = _args[19];
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_methods_2370_, v_____do__lift_2371_, v_____do__lift_2372_, v_____do__lift_2373_, v_x_2374_, v_toPure_2375_, v_inst_2376_, v___f_2377_, v_toBind_2378_, v_setNextMacroScope_2379_, v_inst_2380_, v_inst_2381_, v_inst_2382_, v_toMonadRef_2383_, v_inst_2384_, v_inst_2385_, v_toMonadExceptOf_2386_, v_getNextMacroScope_2387_, v_getMaxRecDepth_2388_, v_____do__lift_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2391_, lean_object* v_methods_2392_, lean_object* v_____do__lift_2393_, lean_object* v_____do__lift_2394_, lean_object* v_x_2395_, lean_object* v_toPure_2396_, lean_object* v_inst_2397_, lean_object* v___f_2398_, lean_object* v_toBind_2399_, lean_object* v_setNextMacroScope_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_toMonadRef_2404_, lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_toMonadExceptOf_2407_, lean_object* v_getNextMacroScope_2408_, lean_object* v_____do__lift_2409_){
_start:
{
lean_object* v_getRecDepth_2410_; lean_object* v_getMaxRecDepth_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; 
v_getRecDepth_2410_ = lean_ctor_get(v_inst_2391_, 1);
lean_inc(v_getRecDepth_2410_);
v_getMaxRecDepth_2411_ = lean_ctor_get(v_inst_2391_, 2);
lean_inc(v_getMaxRecDepth_2411_);
lean_dec_ref(v_inst_2391_);
lean_inc(v_toBind_2399_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 20, 19);
lean_closure_set(v___f_2412_, 0, v_methods_2392_);
lean_closure_set(v___f_2412_, 1, v_____do__lift_2409_);
lean_closure_set(v___f_2412_, 2, v_____do__lift_2393_);
lean_closure_set(v___f_2412_, 3, v_____do__lift_2394_);
lean_closure_set(v___f_2412_, 4, v_x_2395_);
lean_closure_set(v___f_2412_, 5, v_toPure_2396_);
lean_closure_set(v___f_2412_, 6, v_inst_2397_);
lean_closure_set(v___f_2412_, 7, v___f_2398_);
lean_closure_set(v___f_2412_, 8, v_toBind_2399_);
lean_closure_set(v___f_2412_, 9, v_setNextMacroScope_2400_);
lean_closure_set(v___f_2412_, 10, v_inst_2401_);
lean_closure_set(v___f_2412_, 11, v_inst_2402_);
lean_closure_set(v___f_2412_, 12, v_inst_2403_);
lean_closure_set(v___f_2412_, 13, v_toMonadRef_2404_);
lean_closure_set(v___f_2412_, 14, v_inst_2405_);
lean_closure_set(v___f_2412_, 15, v_inst_2406_);
lean_closure_set(v___f_2412_, 16, v_toMonadExceptOf_2407_);
lean_closure_set(v___f_2412_, 17, v_getNextMacroScope_2408_);
lean_closure_set(v___f_2412_, 18, v_getMaxRecDepth_2411_);
v___x_2413_ = lean_apply_4(v_toBind_2399_, lean_box(0), lean_box(0), v_getRecDepth_2410_, v___f_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2414_ = _args[0];
lean_object* v_methods_2415_ = _args[1];
lean_object* v_____do__lift_2416_ = _args[2];
lean_object* v_____do__lift_2417_ = _args[3];
lean_object* v_x_2418_ = _args[4];
lean_object* v_toPure_2419_ = _args[5];
lean_object* v_inst_2420_ = _args[6];
lean_object* v___f_2421_ = _args[7];
lean_object* v_toBind_2422_ = _args[8];
lean_object* v_setNextMacroScope_2423_ = _args[9];
lean_object* v_inst_2424_ = _args[10];
lean_object* v_inst_2425_ = _args[11];
lean_object* v_inst_2426_ = _args[12];
lean_object* v_toMonadRef_2427_ = _args[13];
lean_object* v_inst_2428_ = _args[14];
lean_object* v_inst_2429_ = _args[15];
lean_object* v_toMonadExceptOf_2430_ = _args[16];
lean_object* v_getNextMacroScope_2431_ = _args[17];
lean_object* v_____do__lift_2432_ = _args[18];
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2414_, v_methods_2415_, v_____do__lift_2416_, v_____do__lift_2417_, v_x_2418_, v_toPure_2419_, v_inst_2420_, v___f_2421_, v_toBind_2422_, v_setNextMacroScope_2423_, v_inst_2424_, v_inst_2425_, v_inst_2426_, v_toMonadRef_2427_, v_inst_2428_, v_inst_2429_, v_toMonadExceptOf_2430_, v_getNextMacroScope_2431_, v_____do__lift_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_inst_2434_, lean_object* v_methods_2435_, lean_object* v_____do__lift_2436_, lean_object* v_x_2437_, lean_object* v_toPure_2438_, lean_object* v_inst_2439_, lean_object* v___f_2440_, lean_object* v_toBind_2441_, lean_object* v_setNextMacroScope_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_toMonadRef_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_toMonadExceptOf_2449_, lean_object* v_getNextMacroScope_2450_, lean_object* v_getContext_2451_, lean_object* v_____do__lift_2452_){
_start:
{
lean_object* v___f_2453_; lean_object* v___x_2454_; 
lean_inc(v_toBind_2441_);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2453_, 0, v_inst_2434_);
lean_closure_set(v___f_2453_, 1, v_methods_2435_);
lean_closure_set(v___f_2453_, 2, v_____do__lift_2452_);
lean_closure_set(v___f_2453_, 3, v_____do__lift_2436_);
lean_closure_set(v___f_2453_, 4, v_x_2437_);
lean_closure_set(v___f_2453_, 5, v_toPure_2438_);
lean_closure_set(v___f_2453_, 6, v_inst_2439_);
lean_closure_set(v___f_2453_, 7, v___f_2440_);
lean_closure_set(v___f_2453_, 8, v_toBind_2441_);
lean_closure_set(v___f_2453_, 9, v_setNextMacroScope_2442_);
lean_closure_set(v___f_2453_, 10, v_inst_2443_);
lean_closure_set(v___f_2453_, 11, v_inst_2444_);
lean_closure_set(v___f_2453_, 12, v_inst_2445_);
lean_closure_set(v___f_2453_, 13, v_toMonadRef_2446_);
lean_closure_set(v___f_2453_, 14, v_inst_2447_);
lean_closure_set(v___f_2453_, 15, v_inst_2448_);
lean_closure_set(v___f_2453_, 16, v_toMonadExceptOf_2449_);
lean_closure_set(v___f_2453_, 17, v_getNextMacroScope_2450_);
v___x_2454_ = lean_apply_4(v_toBind_2441_, lean_box(0), lean_box(0), v_getContext_2451_, v___f_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_inst_2455_ = _args[0];
lean_object* v_methods_2456_ = _args[1];
lean_object* v_____do__lift_2457_ = _args[2];
lean_object* v_x_2458_ = _args[3];
lean_object* v_toPure_2459_ = _args[4];
lean_object* v_inst_2460_ = _args[5];
lean_object* v___f_2461_ = _args[6];
lean_object* v_toBind_2462_ = _args[7];
lean_object* v_setNextMacroScope_2463_ = _args[8];
lean_object* v_inst_2464_ = _args[9];
lean_object* v_inst_2465_ = _args[10];
lean_object* v_inst_2466_ = _args[11];
lean_object* v_toMonadRef_2467_ = _args[12];
lean_object* v_inst_2468_ = _args[13];
lean_object* v_inst_2469_ = _args[14];
lean_object* v_toMonadExceptOf_2470_ = _args[15];
lean_object* v_getNextMacroScope_2471_ = _args[16];
lean_object* v_getContext_2472_ = _args[17];
lean_object* v_____do__lift_2473_ = _args[18];
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_inst_2455_, v_methods_2456_, v_____do__lift_2457_, v_x_2458_, v_toPure_2459_, v_inst_2460_, v___f_2461_, v_toBind_2462_, v_setNextMacroScope_2463_, v_inst_2464_, v_inst_2465_, v_inst_2466_, v_toMonadRef_2467_, v_inst_2468_, v_inst_2469_, v_toMonadExceptOf_2470_, v_getNextMacroScope_2471_, v_getContext_2472_, v_____do__lift_2473_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadQuotation_2475_, lean_object* v_inst_2476_, lean_object* v_methods_2477_, lean_object* v_x_2478_, lean_object* v_toPure_2479_, lean_object* v_inst_2480_, lean_object* v___f_2481_, lean_object* v_toBind_2482_, lean_object* v_setNextMacroScope_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_toMonadRef_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_toMonadExceptOf_2490_, lean_object* v_getNextMacroScope_2491_, lean_object* v_____do__lift_2492_){
_start:
{
lean_object* v_getCurrMacroScope_2493_; lean_object* v_getContext_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; 
v_getCurrMacroScope_2493_ = lean_ctor_get(v_toMonadQuotation_2475_, 1);
lean_inc(v_getCurrMacroScope_2493_);
v_getContext_2494_ = lean_ctor_get(v_toMonadQuotation_2475_, 2);
lean_inc(v_getContext_2494_);
lean_dec_ref(v_toMonadQuotation_2475_);
lean_inc(v_toBind_2482_);
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 19, 18);
lean_closure_set(v___f_2495_, 0, v_inst_2476_);
lean_closure_set(v___f_2495_, 1, v_methods_2477_);
lean_closure_set(v___f_2495_, 2, v_____do__lift_2492_);
lean_closure_set(v___f_2495_, 3, v_x_2478_);
lean_closure_set(v___f_2495_, 4, v_toPure_2479_);
lean_closure_set(v___f_2495_, 5, v_inst_2480_);
lean_closure_set(v___f_2495_, 6, v___f_2481_);
lean_closure_set(v___f_2495_, 7, v_toBind_2482_);
lean_closure_set(v___f_2495_, 8, v_setNextMacroScope_2483_);
lean_closure_set(v___f_2495_, 9, v_inst_2484_);
lean_closure_set(v___f_2495_, 10, v_inst_2485_);
lean_closure_set(v___f_2495_, 11, v_inst_2486_);
lean_closure_set(v___f_2495_, 12, v_toMonadRef_2487_);
lean_closure_set(v___f_2495_, 13, v_inst_2488_);
lean_closure_set(v___f_2495_, 14, v_inst_2489_);
lean_closure_set(v___f_2495_, 15, v_toMonadExceptOf_2490_);
lean_closure_set(v___f_2495_, 16, v_getNextMacroScope_2491_);
lean_closure_set(v___f_2495_, 17, v_getContext_2494_);
v___x_2496_ = lean_apply_4(v_toBind_2482_, lean_box(0), lean_box(0), v_getCurrMacroScope_2493_, v___f_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2497_ = _args[0];
lean_object* v_inst_2498_ = _args[1];
lean_object* v_methods_2499_ = _args[2];
lean_object* v_x_2500_ = _args[3];
lean_object* v_toPure_2501_ = _args[4];
lean_object* v_inst_2502_ = _args[5];
lean_object* v___f_2503_ = _args[6];
lean_object* v_toBind_2504_ = _args[7];
lean_object* v_setNextMacroScope_2505_ = _args[8];
lean_object* v_inst_2506_ = _args[9];
lean_object* v_inst_2507_ = _args[10];
lean_object* v_inst_2508_ = _args[11];
lean_object* v_toMonadRef_2509_ = _args[12];
lean_object* v_inst_2510_ = _args[13];
lean_object* v_inst_2511_ = _args[14];
lean_object* v_toMonadExceptOf_2512_ = _args[15];
lean_object* v_getNextMacroScope_2513_ = _args[16];
lean_object* v_____do__lift_2514_ = _args[17];
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadQuotation_2497_, v_inst_2498_, v_methods_2499_, v_x_2500_, v_toPure_2501_, v_inst_2502_, v___f_2503_, v_toBind_2504_, v_setNextMacroScope_2505_, v_inst_2506_, v_inst_2507_, v_inst_2508_, v_toMonadRef_2509_, v_inst_2510_, v_inst_2511_, v_toMonadExceptOf_2512_, v_getNextMacroScope_2513_, v_____do__lift_2514_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2516_, lean_object* v_env_2517_, lean_object* v_currNamespace_2518_, lean_object* v_opts_2519_, lean_object* v___x_2520_, lean_object* v___f_2521_, lean_object* v___f_2522_, lean_object* v_toMonadQuotation_2523_, lean_object* v_inst_2524_, lean_object* v_x_2525_, lean_object* v_toPure_2526_, lean_object* v_inst_2527_, lean_object* v___f_2528_, lean_object* v_toBind_2529_, lean_object* v_setNextMacroScope_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_toMonadExceptOf_2536_, lean_object* v_getNextMacroScope_2537_, lean_object* v_openDecls_2538_){
_start:
{
lean_object* v_getRef_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v_methods_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; 
v_getRef_2539_ = lean_ctor_get(v_toMonadRef_2516_, 0);
lean_inc(v_getRef_2539_);
lean_inc(v_openDecls_2538_);
lean_inc_n(v_currNamespace_2518_, 2);
lean_inc_ref(v_env_2517_);
v___f_2540_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 6, 3);
lean_closure_set(v___f_2540_, 0, v_env_2517_);
lean_closure_set(v___f_2540_, 1, v_currNamespace_2518_);
lean_closure_set(v___f_2540_, 2, v_openDecls_2538_);
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_2541_, 0, v_env_2517_);
lean_closure_set(v___f_2541_, 1, v_opts_2519_);
lean_closure_set(v___f_2541_, 2, v_currNamespace_2518_);
lean_closure_set(v___f_2541_, 3, v_openDecls_2538_);
v___x_2542_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2542_, 0, lean_box(0));
lean_closure_set(v___x_2542_, 1, lean_box(0));
lean_closure_set(v___x_2542_, 2, v___x_2520_);
lean_closure_set(v___x_2542_, 3, lean_box(0));
lean_closure_set(v___x_2542_, 4, v_currNamespace_2518_);
v_methods_2543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2543_, 0, v___f_2521_);
lean_ctor_set(v_methods_2543_, 1, v___x_2542_);
lean_ctor_set(v_methods_2543_, 2, v___f_2522_);
lean_ctor_set(v_methods_2543_, 3, v___f_2540_);
lean_ctor_set(v_methods_2543_, 4, v___f_2541_);
lean_inc(v_toBind_2529_);
v___f_2544_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 18, 17);
lean_closure_set(v___f_2544_, 0, v_toMonadQuotation_2523_);
lean_closure_set(v___f_2544_, 1, v_inst_2524_);
lean_closure_set(v___f_2544_, 2, v_methods_2543_);
lean_closure_set(v___f_2544_, 3, v_x_2525_);
lean_closure_set(v___f_2544_, 4, v_toPure_2526_);
lean_closure_set(v___f_2544_, 5, v_inst_2527_);
lean_closure_set(v___f_2544_, 6, v___f_2528_);
lean_closure_set(v___f_2544_, 7, v_toBind_2529_);
lean_closure_set(v___f_2544_, 8, v_setNextMacroScope_2530_);
lean_closure_set(v___f_2544_, 9, v_inst_2531_);
lean_closure_set(v___f_2544_, 10, v_inst_2532_);
lean_closure_set(v___f_2544_, 11, v_inst_2533_);
lean_closure_set(v___f_2544_, 12, v_toMonadRef_2516_);
lean_closure_set(v___f_2544_, 13, v_inst_2534_);
lean_closure_set(v___f_2544_, 14, v_inst_2535_);
lean_closure_set(v___f_2544_, 15, v_toMonadExceptOf_2536_);
lean_closure_set(v___f_2544_, 16, v_getNextMacroScope_2537_);
v___x_2545_ = lean_apply_4(v_toBind_2529_, lean_box(0), lean_box(0), v_getRef_2539_, v___f_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2546_ = _args[0];
lean_object* v_env_2547_ = _args[1];
lean_object* v_currNamespace_2548_ = _args[2];
lean_object* v_opts_2549_ = _args[3];
lean_object* v___x_2550_ = _args[4];
lean_object* v___f_2551_ = _args[5];
lean_object* v___f_2552_ = _args[6];
lean_object* v_toMonadQuotation_2553_ = _args[7];
lean_object* v_inst_2554_ = _args[8];
lean_object* v_x_2555_ = _args[9];
lean_object* v_toPure_2556_ = _args[10];
lean_object* v_inst_2557_ = _args[11];
lean_object* v___f_2558_ = _args[12];
lean_object* v_toBind_2559_ = _args[13];
lean_object* v_setNextMacroScope_2560_ = _args[14];
lean_object* v_inst_2561_ = _args[15];
lean_object* v_inst_2562_ = _args[16];
lean_object* v_inst_2563_ = _args[17];
lean_object* v_inst_2564_ = _args[18];
lean_object* v_inst_2565_ = _args[19];
lean_object* v_toMonadExceptOf_2566_ = _args[20];
lean_object* v_getNextMacroScope_2567_ = _args[21];
lean_object* v_openDecls_2568_ = _args[22];
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2546_, v_env_2547_, v_currNamespace_2548_, v_opts_2549_, v___x_2550_, v___f_2551_, v___f_2552_, v_toMonadQuotation_2553_, v_inst_2554_, v_x_2555_, v_toPure_2556_, v_inst_2557_, v___f_2558_, v_toBind_2559_, v_setNextMacroScope_2560_, v_inst_2561_, v_inst_2562_, v_inst_2563_, v_inst_2564_, v_inst_2565_, v_toMonadExceptOf_2566_, v_getNextMacroScope_2567_, v_openDecls_2568_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_toMonadRef_2570_, lean_object* v_env_2571_, lean_object* v_opts_2572_, lean_object* v___x_2573_, lean_object* v___f_2574_, lean_object* v___f_2575_, lean_object* v_toMonadQuotation_2576_, lean_object* v_inst_2577_, lean_object* v_x_2578_, lean_object* v_toPure_2579_, lean_object* v_inst_2580_, lean_object* v___f_2581_, lean_object* v_toBind_2582_, lean_object* v_setNextMacroScope_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_toMonadExceptOf_2589_, lean_object* v_getNextMacroScope_2590_, lean_object* v_getOpenDecls_2591_, lean_object* v_currNamespace_2592_){
_start:
{
lean_object* v___f_2593_; lean_object* v___x_2594_; 
lean_inc(v_toBind_2582_);
v___f_2593_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2593_, 0, v_toMonadRef_2570_);
lean_closure_set(v___f_2593_, 1, v_env_2571_);
lean_closure_set(v___f_2593_, 2, v_currNamespace_2592_);
lean_closure_set(v___f_2593_, 3, v_opts_2572_);
lean_closure_set(v___f_2593_, 4, v___x_2573_);
lean_closure_set(v___f_2593_, 5, v___f_2574_);
lean_closure_set(v___f_2593_, 6, v___f_2575_);
lean_closure_set(v___f_2593_, 7, v_toMonadQuotation_2576_);
lean_closure_set(v___f_2593_, 8, v_inst_2577_);
lean_closure_set(v___f_2593_, 9, v_x_2578_);
lean_closure_set(v___f_2593_, 10, v_toPure_2579_);
lean_closure_set(v___f_2593_, 11, v_inst_2580_);
lean_closure_set(v___f_2593_, 12, v___f_2581_);
lean_closure_set(v___f_2593_, 13, v_toBind_2582_);
lean_closure_set(v___f_2593_, 14, v_setNextMacroScope_2583_);
lean_closure_set(v___f_2593_, 15, v_inst_2584_);
lean_closure_set(v___f_2593_, 16, v_inst_2585_);
lean_closure_set(v___f_2593_, 17, v_inst_2586_);
lean_closure_set(v___f_2593_, 18, v_inst_2587_);
lean_closure_set(v___f_2593_, 19, v_inst_2588_);
lean_closure_set(v___f_2593_, 20, v_toMonadExceptOf_2589_);
lean_closure_set(v___f_2593_, 21, v_getNextMacroScope_2590_);
v___x_2594_ = lean_apply_4(v_toBind_2582_, lean_box(0), lean_box(0), v_getOpenDecls_2591_, v___f_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_toMonadRef_2595_ = _args[0];
lean_object* v_env_2596_ = _args[1];
lean_object* v_opts_2597_ = _args[2];
lean_object* v___x_2598_ = _args[3];
lean_object* v___f_2599_ = _args[4];
lean_object* v___f_2600_ = _args[5];
lean_object* v_toMonadQuotation_2601_ = _args[6];
lean_object* v_inst_2602_ = _args[7];
lean_object* v_x_2603_ = _args[8];
lean_object* v_toPure_2604_ = _args[9];
lean_object* v_inst_2605_ = _args[10];
lean_object* v___f_2606_ = _args[11];
lean_object* v_toBind_2607_ = _args[12];
lean_object* v_setNextMacroScope_2608_ = _args[13];
lean_object* v_inst_2609_ = _args[14];
lean_object* v_inst_2610_ = _args[15];
lean_object* v_inst_2611_ = _args[16];
lean_object* v_inst_2612_ = _args[17];
lean_object* v_inst_2613_ = _args[18];
lean_object* v_toMonadExceptOf_2614_ = _args[19];
lean_object* v_getNextMacroScope_2615_ = _args[20];
lean_object* v_getOpenDecls_2616_ = _args[21];
lean_object* v_currNamespace_2617_ = _args[22];
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_toMonadRef_2595_, v_env_2596_, v_opts_2597_, v___x_2598_, v___f_2599_, v___f_2600_, v_toMonadQuotation_2601_, v_inst_2602_, v_x_2603_, v_toPure_2604_, v_inst_2605_, v___f_2606_, v_toBind_2607_, v_setNextMacroScope_2608_, v_inst_2609_, v_inst_2610_, v_inst_2611_, v_inst_2612_, v_inst_2613_, v_toMonadExceptOf_2614_, v_getNextMacroScope_2615_, v_getOpenDecls_2616_, v_currNamespace_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v_inst_2619_, lean_object* v_toMonadRef_2620_, lean_object* v_env_2621_, lean_object* v___x_2622_, lean_object* v___f_2623_, lean_object* v___f_2624_, lean_object* v_toMonadQuotation_2625_, lean_object* v_inst_2626_, lean_object* v_x_2627_, lean_object* v_toPure_2628_, lean_object* v_inst_2629_, lean_object* v___f_2630_, lean_object* v_toBind_2631_, lean_object* v_setNextMacroScope_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_toMonadExceptOf_2638_, lean_object* v_getNextMacroScope_2639_, lean_object* v_opts_2640_){
_start:
{
lean_object* v_getCurrNamespace_2641_; lean_object* v_getOpenDecls_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; 
v_getCurrNamespace_2641_ = lean_ctor_get(v_inst_2619_, 0);
lean_inc(v_getCurrNamespace_2641_);
v_getOpenDecls_2642_ = lean_ctor_get(v_inst_2619_, 1);
lean_inc(v_getOpenDecls_2642_);
lean_dec_ref(v_inst_2619_);
lean_inc(v_toBind_2631_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 23, 22);
lean_closure_set(v___f_2643_, 0, v_toMonadRef_2620_);
lean_closure_set(v___f_2643_, 1, v_env_2621_);
lean_closure_set(v___f_2643_, 2, v_opts_2640_);
lean_closure_set(v___f_2643_, 3, v___x_2622_);
lean_closure_set(v___f_2643_, 4, v___f_2623_);
lean_closure_set(v___f_2643_, 5, v___f_2624_);
lean_closure_set(v___f_2643_, 6, v_toMonadQuotation_2625_);
lean_closure_set(v___f_2643_, 7, v_inst_2626_);
lean_closure_set(v___f_2643_, 8, v_x_2627_);
lean_closure_set(v___f_2643_, 9, v_toPure_2628_);
lean_closure_set(v___f_2643_, 10, v_inst_2629_);
lean_closure_set(v___f_2643_, 11, v___f_2630_);
lean_closure_set(v___f_2643_, 12, v_toBind_2631_);
lean_closure_set(v___f_2643_, 13, v_setNextMacroScope_2632_);
lean_closure_set(v___f_2643_, 14, v_inst_2633_);
lean_closure_set(v___f_2643_, 15, v_inst_2634_);
lean_closure_set(v___f_2643_, 16, v_inst_2635_);
lean_closure_set(v___f_2643_, 17, v_inst_2636_);
lean_closure_set(v___f_2643_, 18, v_inst_2637_);
lean_closure_set(v___f_2643_, 19, v_toMonadExceptOf_2638_);
lean_closure_set(v___f_2643_, 20, v_getNextMacroScope_2639_);
lean_closure_set(v___f_2643_, 21, v_getOpenDecls_2642_);
v___x_2644_ = lean_apply_4(v_toBind_2631_, lean_box(0), lean_box(0), v_getCurrNamespace_2641_, v___f_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_inst_2645_ = _args[0];
lean_object* v_toMonadRef_2646_ = _args[1];
lean_object* v_env_2647_ = _args[2];
lean_object* v___x_2648_ = _args[3];
lean_object* v___f_2649_ = _args[4];
lean_object* v___f_2650_ = _args[5];
lean_object* v_toMonadQuotation_2651_ = _args[6];
lean_object* v_inst_2652_ = _args[7];
lean_object* v_x_2653_ = _args[8];
lean_object* v_toPure_2654_ = _args[9];
lean_object* v_inst_2655_ = _args[10];
lean_object* v___f_2656_ = _args[11];
lean_object* v_toBind_2657_ = _args[12];
lean_object* v_setNextMacroScope_2658_ = _args[13];
lean_object* v_inst_2659_ = _args[14];
lean_object* v_inst_2660_ = _args[15];
lean_object* v_inst_2661_ = _args[16];
lean_object* v_inst_2662_ = _args[17];
lean_object* v_inst_2663_ = _args[18];
lean_object* v_toMonadExceptOf_2664_ = _args[19];
lean_object* v_getNextMacroScope_2665_ = _args[20];
lean_object* v_opts_2666_ = _args[21];
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v_inst_2645_, v_toMonadRef_2646_, v_env_2647_, v___x_2648_, v___f_2649_, v___f_2650_, v_toMonadQuotation_2651_, v_inst_2652_, v_x_2653_, v_toPure_2654_, v_inst_2655_, v___f_2656_, v_toBind_2657_, v_setNextMacroScope_2658_, v_inst_2659_, v_inst_2660_, v_inst_2661_, v_inst_2662_, v_inst_2663_, v_toMonadExceptOf_2664_, v_getNextMacroScope_2665_, v_opts_2666_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__23(lean_object* v_inst_2668_, lean_object* v___x_2669_, lean_object* v___x_2670_, lean_object* v_inst_2671_, lean_object* v_toMonadRef_2672_, lean_object* v___x_2673_, lean_object* v_toMonadQuotation_2674_, lean_object* v_inst_2675_, lean_object* v_x_2676_, lean_object* v_toPure_2677_, lean_object* v_inst_2678_, lean_object* v___f_2679_, lean_object* v_toBind_2680_, lean_object* v_setNextMacroScope_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_toMonadExceptOf_2686_, lean_object* v_getNextMacroScope_2687_, lean_object* v_env_2688_){
_start:
{
lean_object* v_getOptions_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; 
v_getOptions_2689_ = lean_ctor_get(v_inst_2668_, 0);
lean_inc(v_getOptions_2689_);
lean_inc_ref_n(v_env_2688_, 2);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2690_, 0, v_env_2688_);
lean_closure_set(v___f_2690_, 1, v___x_2669_);
lean_closure_set(v___f_2690_, 2, v___x_2670_);
v___f_2691_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 4, 1);
lean_closure_set(v___f_2691_, 0, v_env_2688_);
lean_inc(v_toBind_2680_);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 22, 21);
lean_closure_set(v___f_2692_, 0, v_inst_2671_);
lean_closure_set(v___f_2692_, 1, v_toMonadRef_2672_);
lean_closure_set(v___f_2692_, 2, v_env_2688_);
lean_closure_set(v___f_2692_, 3, v___x_2673_);
lean_closure_set(v___f_2692_, 4, v___f_2690_);
lean_closure_set(v___f_2692_, 5, v___f_2691_);
lean_closure_set(v___f_2692_, 6, v_toMonadQuotation_2674_);
lean_closure_set(v___f_2692_, 7, v_inst_2675_);
lean_closure_set(v___f_2692_, 8, v_x_2676_);
lean_closure_set(v___f_2692_, 9, v_toPure_2677_);
lean_closure_set(v___f_2692_, 10, v_inst_2678_);
lean_closure_set(v___f_2692_, 11, v___f_2679_);
lean_closure_set(v___f_2692_, 12, v_toBind_2680_);
lean_closure_set(v___f_2692_, 13, v_setNextMacroScope_2681_);
lean_closure_set(v___f_2692_, 14, v_inst_2682_);
lean_closure_set(v___f_2692_, 15, v_inst_2683_);
lean_closure_set(v___f_2692_, 16, v_inst_2668_);
lean_closure_set(v___f_2692_, 17, v_inst_2684_);
lean_closure_set(v___f_2692_, 18, v_inst_2685_);
lean_closure_set(v___f_2692_, 19, v_toMonadExceptOf_2686_);
lean_closure_set(v___f_2692_, 20, v_getNextMacroScope_2687_);
v___x_2693_ = lean_apply_4(v_toBind_2680_, lean_box(0), lean_box(0), v_getOptions_2689_, v___f_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_inst_2694_ = _args[0];
lean_object* v___x_2695_ = _args[1];
lean_object* v___x_2696_ = _args[2];
lean_object* v_inst_2697_ = _args[3];
lean_object* v_toMonadRef_2698_ = _args[4];
lean_object* v___x_2699_ = _args[5];
lean_object* v_toMonadQuotation_2700_ = _args[6];
lean_object* v_inst_2701_ = _args[7];
lean_object* v_x_2702_ = _args[8];
lean_object* v_toPure_2703_ = _args[9];
lean_object* v_inst_2704_ = _args[10];
lean_object* v___f_2705_ = _args[11];
lean_object* v_toBind_2706_ = _args[12];
lean_object* v_setNextMacroScope_2707_ = _args[13];
lean_object* v_inst_2708_ = _args[14];
lean_object* v_inst_2709_ = _args[15];
lean_object* v_inst_2710_ = _args[16];
lean_object* v_inst_2711_ = _args[17];
lean_object* v_toMonadExceptOf_2712_ = _args[18];
lean_object* v_getNextMacroScope_2713_ = _args[19];
lean_object* v_env_2714_ = _args[20];
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_liftMacroM___redArg___lam__23(v_inst_2694_, v___x_2695_, v___x_2696_, v_inst_2697_, v_toMonadRef_2698_, v___x_2699_, v_toMonadQuotation_2700_, v_inst_2701_, v_x_2702_, v_toPure_2703_, v_inst_2704_, v___f_2705_, v_toBind_2706_, v_setNextMacroScope_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_toMonadExceptOf_2712_, v_getNextMacroScope_2713_, v_env_2714_);
return v_res_2715_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_EStateM_nonBacktrackable___redArg();
return v___x_2735_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2737_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___f_2739_; 
v___x_2738_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2739_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2739_, 0, v___x_2738_);
return v___f_2739_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___f_2741_; 
v___x_2740_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2741_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2741_, 0, v___x_2740_);
return v___f_2741_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
v___f_2742_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2743_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___f_2743_);
lean_ctor_set(v___x_2744_, 1, v___f_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_x_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v_toApplicative_2759_; lean_object* v_toBind_2760_; lean_object* v_getEnv_2761_; lean_object* v_toMonadExceptOf_2762_; lean_object* v_toMonadRef_2763_; lean_object* v_toMonadQuotation_2764_; lean_object* v_getNextMacroScope_2765_; lean_object* v_setNextMacroScope_2766_; lean_object* v_toPure_2767_; lean_object* v___x_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; 
v___x_2757_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2758_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2759_ = lean_ctor_get(v_inst_2747_, 0);
v_toBind_2760_ = lean_ctor_get(v_inst_2747_, 1);
lean_inc_n(v_toBind_2760_, 3);
v_getEnv_2761_ = lean_ctor_get(v_inst_2749_, 0);
lean_inc(v_getEnv_2761_);
v_toMonadExceptOf_2762_ = lean_ctor_get(v_inst_2751_, 0);
lean_inc_ref(v_toMonadExceptOf_2762_);
v_toMonadRef_2763_ = lean_ctor_get(v_inst_2751_, 1);
lean_inc_ref_n(v_toMonadRef_2763_, 2);
v_toMonadQuotation_2764_ = lean_ctor_get(v_inst_2748_, 0);
lean_inc_ref(v_toMonadQuotation_2764_);
v_getNextMacroScope_2765_ = lean_ctor_get(v_inst_2748_, 1);
lean_inc(v_getNextMacroScope_2765_);
v_setNextMacroScope_2766_ = lean_ctor_get(v_inst_2748_, 2);
lean_inc(v_setNextMacroScope_2766_);
lean_dec_ref(v_inst_2748_);
v_toPure_2767_ = lean_ctor_get(v_toApplicative_2759_, 1);
lean_inc_n(v_toPure_2767_, 2);
v___x_2768_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2755_);
lean_inc_ref(v_inst_2747_);
lean_inc_ref(v_inst_2754_);
lean_inc_ref(v_inst_2753_);
v___f_2769_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2769_, 0, v_inst_2753_);
lean_closure_set(v___f_2769_, 1, v_inst_2754_);
lean_closure_set(v___f_2769_, 2, v_toPure_2767_);
lean_closure_set(v___f_2769_, 3, v_toBind_2760_);
lean_closure_set(v___f_2769_, 4, v_inst_2747_);
lean_closure_set(v___f_2769_, 5, v_toMonadRef_2763_);
lean_closure_set(v___f_2769_, 6, v_inst_2755_);
v___f_2770_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__23___boxed), 21, 20);
lean_closure_set(v___f_2770_, 0, v_inst_2754_);
lean_closure_set(v___f_2770_, 1, v___x_2758_);
lean_closure_set(v___f_2770_, 2, v___x_2768_);
lean_closure_set(v___f_2770_, 3, v_inst_2752_);
lean_closure_set(v___f_2770_, 4, v_toMonadRef_2763_);
lean_closure_set(v___f_2770_, 5, v___x_2757_);
lean_closure_set(v___f_2770_, 6, v_toMonadQuotation_2764_);
lean_closure_set(v___f_2770_, 7, v_inst_2750_);
lean_closure_set(v___f_2770_, 8, v_x_2756_);
lean_closure_set(v___f_2770_, 9, v_toPure_2767_);
lean_closure_set(v___f_2770_, 10, v_inst_2747_);
lean_closure_set(v___f_2770_, 11, v___f_2769_);
lean_closure_set(v___f_2770_, 12, v_toBind_2760_);
lean_closure_set(v___f_2770_, 13, v_setNextMacroScope_2766_);
lean_closure_set(v___f_2770_, 14, v_inst_2749_);
lean_closure_set(v___f_2770_, 15, v_inst_2753_);
lean_closure_set(v___f_2770_, 16, v_inst_2755_);
lean_closure_set(v___f_2770_, 17, v_inst_2751_);
lean_closure_set(v___f_2770_, 18, v_toMonadExceptOf_2762_);
lean_closure_set(v___f_2770_, 19, v_getNextMacroScope_2765_);
v___x_2771_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v_getEnv_2761_, v___f_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2772_, lean_object* v_00_u03b1_2773_, lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2774_, v_inst_2775_, v_inst_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_, v_inst_2780_, v_inst_2781_, v_inst_2782_, v_x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2786_, lean_object* v_00_u03b1_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Elab_liftMacroM(v_m_2786_, v_00_u03b1_2787_, v_inst_2788_, v_inst_2789_, v_inst_2790_, v_inst_2791_, v_inst_2792_, v_inst_2793_, v_inst_2794_, v_inst_2795_, v_inst_2796_, v_inst_2797_, v_x_2798_);
lean_dec(v_inst_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_inst_2807_, lean_object* v_inst_2808_, lean_object* v_x_2809_, lean_object* v_stx_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_apply_1(v_x_2809_, v_stx_2810_);
v___x_2812_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2800_, v_inst_2801_, v_inst_2802_, v_inst_2803_, v_inst_2804_, v_inst_2805_, v_inst_2806_, v_inst_2807_, v_inst_2808_, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_x_2824_, lean_object* v_stx_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_apply_1(v_x_2824_, v_stx_2825_);
v___x_2827_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2814_, v_inst_2815_, v_inst_2816_, v_inst_2817_, v_inst_2818_, v_inst_2819_, v_inst_2820_, v_inst_2821_, v_inst_2822_, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_x_2839_, lean_object* v_stx_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_adaptMacro(v_m_2828_, v_inst_2829_, v_inst_2830_, v_inst_2831_, v_inst_2832_, v_inst_2833_, v_inst_2834_, v_inst_2835_, v_inst_2836_, v_inst_2837_, v_inst_2838_, v_x_2839_, v_stx_2840_);
lean_dec(v_inst_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2842_, lean_object* v_currNamespace_2843_, lean_object* v_idx_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_name_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_inc(v_idx_2844_);
lean_inc(v_baseName_2842_);
v_name_2847_ = lean_name_append_index_after(v_baseName_2842_, v_idx_2844_);
lean_inc(v_name_2847_);
lean_inc(v_currNamespace_2843_);
v___x_2848_ = l_Lean_Name_append(v_currNamespace_2843_, v_name_2847_);
v___x_2849_ = l_Lean_Macro_hasDecl(v___x_2848_, v_a_2845_, v_a_2846_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; uint8_t v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v___x_2851_ = lean_unbox(v_a_2850_);
if (v___x_2851_ == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_idx_2844_);
lean_dec(v_currNamespace_2843_);
lean_dec(v_baseName_2842_);
v_a_2852_ = lean_ctor_get(v___x_2849_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___x_2849_, 0);
lean_dec(v_unused_2860_);
v___x_2854_ = v___x_2849_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2849_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v_name_2847_);
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_name_2847_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec(v_name_2847_);
v_a_2861_ = lean_ctor_get(v___x_2849_, 1);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2849_, 2);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_add(v_idx_2844_, v___x_2862_);
lean_dec(v_idx_2844_);
v_idx_2844_ = v___x_2863_;
v_a_2846_ = v_a_2861_;
goto _start;
}
}
else
{
lean_object* v_a_2865_; lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_name_2847_);
lean_dec(v_idx_2844_);
lean_dec(v_currNamespace_2843_);
lean_dec(v_baseName_2842_);
v_a_2865_ = lean_ctor_get(v___x_2849_, 0);
v_a_2866_ = lean_ctor_get(v___x_2849_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2849_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_inc(v_a_2865_);
lean_dec(v___x_2849_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2865_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2874_, lean_object* v_currNamespace_2875_, lean_object* v_idx_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2874_, v_currNamespace_2875_, v_idx_2876_, v_a_2877_, v_a_2878_);
lean_dec_ref(v_a_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Macro_getCurrNamespace(v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_n(v_a_2884_, 2);
v_a_2885_ = lean_ctor_get(v___x_2883_, 1);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2883_, 2);
lean_inc(v_baseName_2880_);
v___x_2886_ = l_Lean_Name_append(v_a_2884_, v_baseName_2880_);
v___x_2887_ = l_Lean_Macro_hasDecl(v___x_2886_, v_a_2881_, v_a_2885_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; uint8_t v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v___x_2889_ = lean_unbox(v_a_2888_);
if (v___x_2889_ == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2884_);
v_a_2890_ = lean_ctor_get(v___x_2887_, 1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2887_, 0);
lean_dec(v_unused_2898_);
v___x_2892_ = v___x_2887_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2887_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_baseName_2880_);
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_baseName_2880_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_a_2899_ = lean_ctor_get(v___x_2887_, 1);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2887_, 2);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2880_, v_a_2884_, v___x_2900_, v_a_2881_, v_a_2899_);
return v___x_2901_;
}
}
else
{
lean_object* v_a_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2884_);
lean_dec(v_baseName_2880_);
v_a_2902_ = lean_ctor_get(v___x_2887_, 0);
v_a_2903_ = lean_ctor_get(v___x_2887_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2887_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_inc(v_a_2902_);
lean_dec(v___x_2887_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2902_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_dec(v_baseName_2880_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2911_, v_a_2912_, v_a_2913_);
lean_dec_ref(v_a_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(lean_object* v_inst_2915_, lean_object* v_name_2916_, lean_object* v_avoid_2917_, lean_object* v_env_2918_, lean_object* v_idx_2919_){
_start:
{
lean_object* v_toApplicative_2920_; lean_object* v_toPure_2921_; lean_object* v_name_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_toApplicative_2920_ = lean_ctor_get(v_inst_2915_, 0);
v_toPure_2921_ = lean_ctor_get(v_toApplicative_2920_, 1);
lean_inc(v_idx_2919_);
lean_inc(v_name_2916_);
v_name_2922_ = lean_name_append_index_after(v_name_2916_, v_idx_2919_);
lean_inc_ref(v_avoid_2917_);
lean_inc(v_name_2922_);
lean_inc_ref(v_env_2918_);
v___x_2923_ = lean_apply_2(v_avoid_2917_, v_env_2918_, v_name_2922_);
v___x_2924_ = lean_unbox(v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
lean_inc(v_toPure_2921_);
lean_dec(v_idx_2919_);
lean_dec_ref(v_env_2918_);
lean_dec_ref(v_avoid_2917_);
lean_dec(v_name_2916_);
lean_dec_ref(v_inst_2915_);
v___x_2925_ = lean_apply_2(v_toPure_2921_, lean_box(0), v_name_2922_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v_name_2922_);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_idx_2919_, v___x_2926_);
lean_dec(v_idx_2919_);
v_idx_2919_ = v___x_2927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop(lean_object* v_m_2929_, lean_object* v_inst_2930_, lean_object* v_name_2931_, lean_object* v_avoid_2932_, lean_object* v_env_2933_, lean_object* v_idx_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(v_inst_2930_, v_name_2931_, v_avoid_2932_, v_env_2933_, v_idx_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg___lam__0(lean_object* v_avoid_2936_, lean_object* v_name_2937_, lean_object* v_toPure_2938_, lean_object* v_inst_2939_, lean_object* v_env_2940_){
_start:
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
lean_inc_ref(v_avoid_2936_);
lean_inc(v_name_2937_);
lean_inc_ref(v_env_2940_);
v___x_2941_ = lean_apply_2(v_avoid_2936_, v_env_2940_, v_name_2937_);
v___x_2942_ = lean_unbox(v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v_env_2940_);
lean_dec_ref(v_inst_2939_);
lean_dec_ref(v_avoid_2936_);
v___x_2943_ = lean_apply_2(v_toPure_2938_, lean_box(0), v_name_2937_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v_toPure_2938_);
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(v_inst_2939_, v_name_2937_, v_avoid_2936_, v_env_2940_, v___x_2944_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg(lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_name_2948_, lean_object* v_avoid_2949_){
_start:
{
lean_object* v_toApplicative_2950_; lean_object* v_toBind_2951_; lean_object* v_getEnv_2952_; lean_object* v_toPure_2953_; lean_object* v___f_2954_; lean_object* v___x_2955_; 
v_toApplicative_2950_ = lean_ctor_get(v_inst_2946_, 0);
v_toBind_2951_ = lean_ctor_get(v_inst_2946_, 1);
lean_inc(v_toBind_2951_);
v_getEnv_2952_ = lean_ctor_get(v_inst_2947_, 0);
lean_inc(v_getEnv_2952_);
lean_dec_ref(v_inst_2947_);
v_toPure_2953_ = lean_ctor_get(v_toApplicative_2950_, 1);
lean_inc(v_toPure_2953_);
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_findUnusedName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2954_, 0, v_avoid_2949_);
lean_closure_set(v___f_2954_, 1, v_name_2948_);
lean_closure_set(v___f_2954_, 2, v_toPure_2953_);
lean_closure_set(v___f_2954_, 3, v_inst_2946_);
v___x_2955_ = lean_apply_4(v_toBind_2951_, lean_box(0), lean_box(0), v_getEnv_2952_, v___f_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName(lean_object* v_m_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_name_2959_, lean_object* v_avoid_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Elab_findUnusedName___redArg(v_inst_2957_, v_inst_2958_, v_name_2959_, v_avoid_2960_);
return v___x_2961_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_name_2969_){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2971_ = l_Lean_MessageData_ofName(v_name_2969_);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_logError___redArg(v_inst_2965_, v_inst_2966_, v_inst_2967_, v_inst_2968_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_ex_2979_){
_start:
{
lean_object* v_toApplicative_2980_; lean_object* v_toBind_2981_; lean_object* v_toPure_2982_; 
v_toApplicative_2980_ = lean_ctor_get(v_inst_2974_, 0);
v_toBind_2981_ = lean_ctor_get(v_inst_2974_, 1);
v_toPure_2982_ = lean_ctor_get(v_toApplicative_2980_, 1);
if (lean_obj_tag(v_ex_2979_) == 0)
{
lean_object* v_ref_2986_; lean_object* v_msg_2987_; lean_object* v___x_2988_; 
lean_dec(v_inst_2978_);
v_ref_2986_ = lean_ctor_get(v_ex_2979_, 0);
lean_inc(v_ref_2986_);
v_msg_2987_ = lean_ctor_get(v_ex_2979_, 1);
lean_inc_ref(v_msg_2987_);
lean_dec_ref_known(v_ex_2979_, 2);
v___x_2988_ = l_Lean_logErrorAt___redArg(v_inst_2974_, v_inst_2975_, v_inst_2976_, v_inst_2977_, v_ref_2986_, v_msg_2987_);
return v___x_2988_;
}
else
{
lean_object* v_id_2989_; uint8_t v___x_2990_; 
lean_inc(v_toBind_2981_);
v_id_2989_ = lean_ctor_get(v_ex_2979_, 0);
lean_inc(v_id_2989_);
v___x_2990_ = l_Lean_Elab_isAbortExceptionId(v_id_2989_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; 
v___x_2991_ = l_Lean_Exception_isInterrupt(v_ex_2979_);
lean_dec_ref_known(v_ex_2979_, 2);
if (v___x_2991_ == 0)
{
lean_object* v___f_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2992_, 0, v_inst_2974_);
lean_closure_set(v___f_2992_, 1, v_inst_2975_);
lean_closure_set(v___f_2992_, 2, v_inst_2976_);
lean_closure_set(v___f_2992_, 3, v_inst_2977_);
v___x_2993_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2993_, 0, v_id_2989_);
v___x_2994_ = lean_apply_2(v_inst_2978_, lean_box(0), v___x_2993_);
v___x_2995_ = lean_apply_4(v_toBind_2981_, lean_box(0), lean_box(0), v___x_2994_, v___f_2992_);
return v___x_2995_;
}
else
{
lean_inc(v_toPure_2982_);
lean_dec(v_id_2989_);
lean_dec(v_toBind_2981_);
lean_dec(v_inst_2978_);
lean_dec_ref(v_inst_2977_);
lean_dec(v_inst_2976_);
lean_dec_ref(v_inst_2975_);
lean_dec_ref(v_inst_2974_);
goto v___jp_2983_;
}
}
else
{
lean_inc(v_toPure_2982_);
lean_dec(v_id_2989_);
lean_dec_ref_known(v_ex_2979_, 2);
lean_dec(v_toBind_2981_);
lean_dec(v_inst_2978_);
lean_dec_ref(v_inst_2977_);
lean_dec(v_inst_2976_);
lean_dec_ref(v_inst_2975_);
lean_dec_ref(v_inst_2974_);
goto v___jp_2983_;
}
}
v___jp_2983_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_apply_2(v_toPure_2982_, lean_box(0), v___x_2984_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_ex_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Elab_logException___redArg(v_inst_2997_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_inst_3001_, v_ex_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_ex_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Elab_logException___redArg(v_inst_3004_, v_inst_3005_, v_inst_3006_, v_inst_3007_, v_inst_3008_, v_ex_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_x_3017_){
_start:
{
lean_object* v_tryCatch_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; 
v_tryCatch_3018_ = lean_ctor_get(v_inst_3013_, 1);
lean_inc(v_tryCatch_3018_);
lean_dec_ref(v_inst_3013_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_3019_, 0, v_inst_3011_);
lean_closure_set(v___f_3019_, 1, v_inst_3012_);
lean_closure_set(v___f_3019_, 2, v_inst_3014_);
lean_closure_set(v___f_3019_, 3, v_inst_3015_);
lean_closure_set(v___f_3019_, 4, v_inst_3016_);
v___x_3020_ = lean_apply_3(v_tryCatch_3018_, lean_box(0), v_x_3017_, v___f_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Elab_withLogging___redArg(v_inst_3022_, v_inst_3023_, v_inst_3024_, v_inst_3025_, v_inst_3026_, v_inst_3027_, v_x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_3033_, lean_object* v_ex_3034_, lean_object* v_toPure_3035_, lean_object* v_____do__lift_3036_){
_start:
{
lean_object* v_exPosition_3037_; lean_object* v_line_3038_; lean_object* v_column_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3059_; 
v_exPosition_3037_ = l_Lean_FileMap_toPosition(v_____do__lift_3036_, v_val_3033_);
v_line_3038_ = lean_ctor_get(v_exPosition_3037_, 0);
v_column_3039_ = lean_ctor_get(v_exPosition_3037_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_exPosition_3037_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3041_ = v_exPosition_3037_;
v_isShared_3042_ = v_isSharedCheck_3059_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_column_3039_);
lean_inc(v_line_3038_);
lean_dec(v_exPosition_3037_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3059_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3043_ = l_Nat_reprFast(v_line_3038_);
v___x_3044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
v___x_3045_ = l_Lean_MessageData_ofFormat(v___x_3044_);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 7);
lean_ctor_set(v___x_3041_, 1, v___x_3046_);
lean_ctor_set(v___x_3041_, 0, v___x_3045_);
v___x_3048_ = v___x_3041_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3049_ = l_Nat_reprFast(v_column_3039_);
v___x_3050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
v___x_3051_ = l_Lean_MessageData_ofFormat(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3048_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_Exception_toMessageData(v_ex_3034_);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_apply_2(v_toPure_3035_, lean_box(0), v___x_3056_);
return v___x_3057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_3060_, lean_object* v_ex_3061_, lean_object* v_toPure_3062_, lean_object* v_____do__lift_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_3060_, v_ex_3061_, v_toPure_3062_, v_____do__lift_3063_);
lean_dec(v_val_3060_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_3065_, lean_object* v_toPure_3066_, lean_object* v_toBind_3067_, lean_object* v_toMonadFileMap_3068_, lean_object* v_pos_3069_){
_start:
{
lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = l_Lean_Exception_getRef(v_ex_3065_);
v___x_3071_ = 0;
v___x_3072_ = l_Lean_Syntax_getPos_x3f(v___x_3070_, v___x_3071_);
lean_dec(v___x_3070_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v_toMonadFileMap_3068_);
lean_dec(v_toBind_3067_);
v___x_3073_ = l_Lean_Exception_toMessageData(v_ex_3065_);
v___x_3074_ = lean_apply_2(v_toPure_3066_, lean_box(0), v___x_3073_);
return v___x_3074_;
}
else
{
lean_object* v_val_3075_; uint8_t v_decide_3076_; 
v_val_3075_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v___x_3072_, 1);
v_decide_3076_ = lean_nat_dec_eq(v_pos_3069_, v_val_3075_);
if (v_decide_3076_ == 0)
{
lean_object* v___f_3077_; lean_object* v___x_3078_; 
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3077_, 0, v_val_3075_);
lean_closure_set(v___f_3077_, 1, v_ex_3065_);
lean_closure_set(v___f_3077_, 2, v_toPure_3066_);
v___x_3078_ = lean_apply_4(v_toBind_3067_, lean_box(0), lean_box(0), v_toMonadFileMap_3068_, v___f_3077_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v_val_3075_);
lean_dec(v_toMonadFileMap_3068_);
lean_dec(v_toBind_3067_);
v___x_3079_ = l_Lean_Exception_toMessageData(v_ex_3065_);
v___x_3080_ = lean_apply_2(v_toPure_3066_, lean_box(0), v___x_3079_);
return v___x_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_3081_, lean_object* v_toPure_3082_, lean_object* v_toBind_3083_, lean_object* v_toMonadFileMap_3084_, lean_object* v_pos_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_3081_, v_toPure_3082_, v_toBind_3083_, v_toMonadFileMap_3084_, v_pos_3085_);
lean_dec(v_pos_3085_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_ex_3089_){
_start:
{
lean_object* v_toApplicative_3090_; lean_object* v_toBind_3091_; lean_object* v_toPure_3092_; lean_object* v_toMonadFileMap_3093_; lean_object* v___x_3094_; lean_object* v___f_3095_; lean_object* v___x_3096_; 
v_toApplicative_3090_ = lean_ctor_get(v_inst_3087_, 0);
v_toBind_3091_ = lean_ctor_get(v_inst_3087_, 1);
lean_inc_n(v_toBind_3091_, 2);
v_toPure_3092_ = lean_ctor_get(v_toApplicative_3090_, 1);
lean_inc(v_toPure_3092_);
v_toMonadFileMap_3093_ = lean_ctor_get(v_inst_3088_, 0);
lean_inc(v_toMonadFileMap_3093_);
v___x_3094_ = l_Lean_getRefPos___redArg(v_inst_3087_, v_inst_3088_);
v___f_3095_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3095_, 0, v_ex_3089_);
lean_closure_set(v___f_3095_, 1, v_toPure_3092_);
lean_closure_set(v___f_3095_, 2, v_toBind_3091_);
lean_closure_set(v___f_3095_, 3, v_toMonadFileMap_3093_);
v___x_3096_ = lean_apply_4(v_toBind_3091_, lean_box(0), lean_box(0), v___x_3094_, v___f_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_ex_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3098_, v_inst_3099_, v_ex_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_x_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3102_, v_inst_3103_, v_x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_____do__lift_3112_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3113_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_3114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_msg_3109_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = l_Lean_toMessageList(v_____do__lift_3112_);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_throwError___redArg(v_inst_3110_, v_inst_3111_, v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_msg_3121_, lean_object* v_exs_3122_){
_start:
{
lean_object* v_toBind_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; size_t v_sz_3126_; size_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_toBind_3123_ = lean_ctor_get(v_inst_3119_, 1);
lean_inc(v_toBind_3123_);
lean_inc_ref_n(v_inst_3119_, 2);
v___f_3124_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3124_, 0, v_inst_3119_);
lean_closure_set(v___f_3124_, 1, v_inst_3120_);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3125_, 0, v_msg_3121_);
lean_closure_set(v___f_3125_, 1, v_inst_3119_);
lean_closure_set(v___f_3125_, 2, v_inst_3118_);
v_sz_3126_ = lean_array_size(v_exs_3122_);
v___x_3127_ = ((size_t)0ULL);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3119_, v___f_3124_, v_sz_3126_, v___x_3127_, v_exs_3122_);
v___x_3129_ = lean_apply_4(v_toBind_3123_, lean_box(0), lean_box(0), v___x_3128_, v___f_3125_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_3130_, lean_object* v_00_u03b1_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_msg_3135_, lean_object* v_exs_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_3132_, v_inst_3133_, v_inst_3134_, v_msg_3135_, v_exs_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3204_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3205_ = 0;
v___x_3206_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3207_ = l_Lean_registerTraceClass(v___x_3204_, v___x_3205_, v___x_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref_known(v___x_3207_, 1);
v___x_3208_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3209_ = l_Lean_registerTraceClass(v___x_3208_, v___x_3205_, v___x_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; uint8_t v___x_3211_; lean_object* v___x_3212_; 
lean_dec_ref_known(v___x_3209_, 1);
v___x_3210_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3211_ = 1;
v___x_3212_ = l_Lean_registerTraceClass(v___x_3210_, v___x_3211_, v___x_3206_);
return v___x_3212_;
}
else
{
return v___x_3209_;
}
}
else
{
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3214_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_pp_macroStack = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_pp_macroStack);
lean_dec_ref(res);
res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instMonadMacroAdapterCoreM = _init_l_Lean_Elab_instMonadMacroAdapterCoreM();
lean_mark_persistent(l_Lean_Elab_instMonadMacroAdapterCoreM);
res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_mkElabAttribute___auto__1 = _init_l_Lean_Elab_mkElabAttribute___auto__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* initialize_Lean_BuiltinDocAttr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Util(builtin);
}
#ifdef __cplusplus
}
#endif
