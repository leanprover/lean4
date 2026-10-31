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
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_privateToUserName(lean_object*);
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
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object**);
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
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_383_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_ctor_set(v___x_385_, 2, v___x_384_);
lean_ctor_set(v___x_385_, 3, v___x_384_);
lean_ctor_set(v___x_385_, 4, v___x_383_);
lean_ctor_set(v___x_385_, 5, v___x_383_);
lean_ctor_set(v___x_385_, 6, v___x_383_);
lean_ctor_set(v___x_385_, 7, v___x_383_);
lean_ctor_set(v___x_385_, 8, v___x_383_);
lean_ctor_set(v___x_385_, 9, v___x_383_);
lean_ctor_set(v___x_385_, 10, v___x_383_);
lean_ctor_set(v___x_385_, 11, v___x_382_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_unsigned_to_nat(32u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((size_t)5ULL);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_unsigned_to_nat(32u);
v___x_392_ = lean_mk_empty_array_with_capacity(v___x_391_);
v___x_393_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_394_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_390_);
lean_ctor_set(v___x_394_, 3, v___x_390_);
lean_ctor_set_usize(v___x_394_, 4, v___x_389_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(1);
v___x_396_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_toCold_404_; lean_object* v_env_405_; lean_object* v_options_406_; uint8_t v___x_407_; lean_object* v_env_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_toCold_404_ = lean_ctor_get(v___y_400_, 0);
v_env_405_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_405_);
lean_dec(v___x_403_);
v_options_406_ = lean_ctor_get(v_toCold_404_, 2);
v___x_407_ = 0;
v_env_408_ = l_Lean_Environment_setRecordingDeps(v_env_405_, v___x_407_);
v___x_409_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_406_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_408_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
lean_ctor_set(v___x_411_, 2, v___x_410_);
lean_ctor_set(v___x_411_, 3, v_options_406_);
v___x_412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_msgData_399_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_ref_423_; lean_object* v___x_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_ref_423_ = lean_ctor_get(v___y_420_, 2);
v___x_424_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_419_, v___y_420_, v___y_421_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc(v_ref_423_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_ref_423_);
lean_ctor_set(v___x_429_, 1, v_a_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 1);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___x_448_; lean_object* v_env_449_; uint8_t v___x_450_; 
v___x_448_ = lean_st_ref_get(v___y_441_);
v_env_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_env_449_);
lean_dec(v___x_448_);
lean_inc(v_k_439_);
v___x_450_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_449_, v_k_439_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v_env_452_; uint8_t v_isExporting_453_; 
v___x_451_ = lean_st_ref_get(v___y_441_);
v_env_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_env_452_);
lean_dec(v___x_451_);
v_isExporting_453_ = lean_ctor_get_uint8(v_env_452_, sizeof(void*)*13);
lean_dec_ref(v_env_452_);
if (v_isExporting_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_isPrivateName(v_k_439_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v_env_456_; lean_object* v_k_457_; lean_object* v___x_458_; lean_object* v_env_459_; uint8_t v___x_460_; 
v___x_455_ = lean_st_ref_get(v___y_441_);
v_env_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_456_);
lean_dec(v___x_455_);
v_k_457_ = l_Lean_mkPrivateName(v_env_456_, v_k_439_);
lean_dec_ref(v_env_456_);
v___x_458_ = lean_st_ref_get(v___y_441_);
v_env_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_459_);
lean_dec(v___x_458_);
lean_inc(v_k_457_);
v___x_460_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_459_, v_k_457_);
if (v___x_460_ == 0)
{
lean_dec(v_k_457_);
v___y_444_ = v___y_440_;
v___y_445_ = v___y_441_;
goto v___jp_443_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_k_457_);
return v___x_461_;
}
}
else
{
lean_dec(v_k_439_);
v___y_444_ = v___y_440_;
v___y_445_ = v___y_441_;
goto v___jp_443_;
}
}
else
{
lean_dec(v_k_439_);
v___y_444_ = v___y_440_;
v___y_445_ = v___y_441_;
goto v___jp_443_;
}
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_k_439_);
return v___x_462_;
}
v___jp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_447_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_446_, v___y_444_, v___y_445_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_468_, lean_object* v_x_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
switch(lean_obj_tag(v_x_469_))
{
case 1:
{
lean_object* v_pre_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_pre_473_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_pre_473_);
lean_inc(v_k_468_);
v___x_474_ = l_Lean_Name_append(v_x_469_, v_k_468_);
v___x_475_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_474_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_dec(v_pre_473_);
lean_dec(v_k_468_);
return v___x_475_;
}
else
{
lean_object* v_a_476_; uint8_t v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v___x_477_ = l_Lean_Exception_isInterrupt(v_a_476_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
lean_inc(v_a_476_);
v___x_478_ = l_Lean_Exception_isRuntime(v_a_476_);
if (v___x_478_ == 0)
{
lean_dec_ref_known(v___x_475_, 1);
v_x_469_ = v_pre_473_;
goto _start;
}
else
{
lean_dec(v_pre_473_);
lean_dec(v_k_468_);
return v___x_475_;
}
}
else
{
lean_dec(v_pre_473_);
lean_dec(v_k_468_);
return v___x_475_;
}
}
}
case 0:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_468_, v___y_470_, v___y_471_);
return v___x_480_;
}
default: 
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_x_469_);
lean_dec(v_k_468_);
v___x_481_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_482_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_481_, v___y_470_, v___y_471_);
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_483_, v_x_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_toCold_493_; lean_object* v_currNamespace_494_; lean_object* v___x_495_; 
v_toCold_493_ = lean_ctor_get(v_a_490_, 0);
v_currNamespace_494_ = lean_ctor_get(v_toCold_493_, 4);
lean_inc(v_currNamespace_494_);
v___x_495_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_489_, v_currNamespace_494_, v_a_490_, v_a_491_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_501_, lean_object* v_msg_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_502_, v___y_503_, v___y_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_507_, lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_507_, v_msg_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_519_, lean_object* v_stx_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Attribute_Builtin_getId(v_stx_520_, v_a_521_, v_a_522_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_n(v_a_525_, 2);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_525_, v_a_521_, v_a_522_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec(v_a_525_);
lean_dec(v_defaultParserNamespace_519_);
return v___x_526_;
}
else
{
lean_object* v_a_527_; uint8_t v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v___x_528_ = l_Lean_Exception_isInterrupt(v_a_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; 
lean_inc(v_a_527_);
v___x_529_ = l_Lean_Exception_isRuntime(v_a_527_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec_ref_known(v___x_526_, 1);
lean_inc(v_a_525_);
v___x_530_ = l_Lean_Name_append(v_defaultParserNamespace_519_, v_a_525_);
v___x_531_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_530_, v_a_521_, v_a_522_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_dec(v_a_525_);
return v___x_531_;
}
else
{
lean_object* v_a_532_; uint8_t v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v___x_533_ = l_Lean_Exception_isInterrupt(v_a_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
lean_inc(v_a_532_);
v___x_534_ = l_Lean_Exception_isRuntime(v_a_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref_known(v___x_531_, 1);
v___x_535_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_536_ = l_Lean_MessageData_ofName(v_a_525_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_539_, v_a_521_, v_a_522_);
return v___x_540_;
}
else
{
lean_dec(v_a_525_);
return v___x_531_;
}
}
else
{
lean_dec(v_a_525_);
return v___x_531_;
}
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_defaultParserNamespace_519_);
return v___x_526_;
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_defaultParserNamespace_519_);
return v___x_526_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_519_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_541_, lean_object* v_stx_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_541_, v_stx_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_551_, lean_object* v_opts_552_, lean_object* v_constName_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_555_ = l_Lean_Environment_evalConstCheck___redArg(v_env_551_, v_opts_552_, v___x_554_, v_constName_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_556_, lean_object* v_opts_557_, lean_object* v_constName_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_556_, v_opts_557_, v_constName_558_);
lean_dec_ref(v_opts_557_);
return v_res_559_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_585_ = l_Lean_mkAtom(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_587_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_588_ = lean_array_push(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_598_ = l_Lean_mkAtom(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_600_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_601_ = lean_array_push(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_603_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_604_ = lean_box(2);
v___x_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
lean_ctor_set(v___x_605_, 2, v___x_602_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_607_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_608_ = lean_array_push(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_610_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_611_ = lean_box(2);
v___x_612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_609_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_614_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_615_ = lean_array_push(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_617_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_618_ = lean_box(2);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_621_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_622_ = lean_array_push(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_624_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_625_ = lean_box(2);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_628_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_629_ = lean_array_push(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_631_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_632_ = lean_box(2);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_630_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_635_, lean_object* v_declName_636_, lean_object* v_kind_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
if (v_builtin_635_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_declName_636_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_636_, v___y_638_, v___y_639_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_644_, lean_object* v_declName_645_, lean_object* v_kind_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
uint8_t v_builtin_boxed_650_; lean_object* v_res_651_; 
v_builtin_boxed_650_ = lean_unbox(v_builtin_644_);
v_res_651_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_650_, v_declName_645_, v_kind_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v_kind_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v_infoState_656_; uint8_t v_enabled_657_; 
v___x_655_ = lean_st_ref_get(v___y_653_);
v_infoState_656_ = lean_ctor_get(v___x_655_, 8);
lean_inc_ref(v_infoState_656_);
lean_dec(v___x_655_);
v_enabled_657_ = lean_ctor_get_uint8(v_infoState_656_, sizeof(void*)*3);
lean_dec_ref(v_infoState_656_);
if (v_enabled_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec_ref(v_t_652_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v_infoState_661_; lean_object* v_env_662_; lean_object* v_nextMacroScope_663_; lean_object* v_ngen_664_; lean_object* v_auxDeclNGen_665_; lean_object* v_traceState_666_; lean_object* v_cache_667_; lean_object* v_recordedDeps_668_; lean_object* v_messages_669_; lean_object* v_snapshotTasks_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_692_; 
v___x_660_ = lean_st_ref_take(v___y_653_);
v_infoState_661_ = lean_ctor_get(v___x_660_, 8);
v_env_662_ = lean_ctor_get(v___x_660_, 0);
v_nextMacroScope_663_ = lean_ctor_get(v___x_660_, 1);
v_ngen_664_ = lean_ctor_get(v___x_660_, 2);
v_auxDeclNGen_665_ = lean_ctor_get(v___x_660_, 3);
v_traceState_666_ = lean_ctor_get(v___x_660_, 4);
v_cache_667_ = lean_ctor_get(v___x_660_, 5);
v_recordedDeps_668_ = lean_ctor_get(v___x_660_, 6);
v_messages_669_ = lean_ctor_get(v___x_660_, 7);
v_snapshotTasks_670_ = lean_ctor_get(v___x_660_, 9);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_692_ == 0)
{
v___x_672_ = v___x_660_;
v_isShared_673_ = v_isSharedCheck_692_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snapshotTasks_670_);
lean_inc(v_infoState_661_);
lean_inc(v_messages_669_);
lean_inc(v_recordedDeps_668_);
lean_inc(v_cache_667_);
lean_inc(v_traceState_666_);
lean_inc(v_auxDeclNGen_665_);
lean_inc(v_ngen_664_);
lean_inc(v_nextMacroScope_663_);
lean_inc(v_env_662_);
lean_dec(v___x_660_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_692_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
uint8_t v_enabled_674_; lean_object* v_assignment_675_; lean_object* v_lazyAssignment_676_; lean_object* v_trees_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_691_; 
v_enabled_674_ = lean_ctor_get_uint8(v_infoState_661_, sizeof(void*)*3);
v_assignment_675_ = lean_ctor_get(v_infoState_661_, 0);
v_lazyAssignment_676_ = lean_ctor_get(v_infoState_661_, 1);
v_trees_677_ = lean_ctor_get(v_infoState_661_, 2);
v_isSharedCheck_691_ = !lean_is_exclusive(v_infoState_661_);
if (v_isSharedCheck_691_ == 0)
{
v___x_679_ = v_infoState_661_;
v_isShared_680_ = v_isSharedCheck_691_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_trees_677_);
lean_inc(v_lazyAssignment_676_);
lean_inc(v_assignment_675_);
lean_dec(v_infoState_661_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_691_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_Lean_PersistentArray_push___redArg(v_trees_677_, v_t_652_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 2, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_assignment_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_lazyAssignment_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___x_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_690_, sizeof(void*)*3, v_enabled_674_);
v___x_684_ = v_reuseFailAlloc_690_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 8, v___x_684_);
v___x_686_ = v___x_672_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_env_662_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_nextMacroScope_663_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_ngen_664_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_auxDeclNGen_665_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_traceState_666_);
lean_ctor_set(v_reuseFailAlloc_689_, 5, v_cache_667_);
lean_ctor_set(v_reuseFailAlloc_689_, 6, v_recordedDeps_668_);
lean_ctor_set(v_reuseFailAlloc_689_, 7, v_messages_669_);
lean_ctor_set(v_reuseFailAlloc_689_, 8, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_689_, 9, v_snapshotTasks_670_);
v___x_686_ = v_reuseFailAlloc_689_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_st_ref_put(v___y_653_, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_681_);
return v___x_688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_693_, v___y_694_);
lean_dec(v___y_694_);
return v_res_696_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(32u);
v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_unsigned_to_nat(32u);
v___x_703_ = lean_mk_empty_array_with_capacity(v___x_702_);
v___x_704_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_705_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_701_);
lean_ctor_set(v___x_705_, 3, v___x_701_);
lean_ctor_set_usize(v___x_705_, 4, v___x_700_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_infoState_711_; uint8_t v_enabled_712_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_infoState_711_ = lean_ctor_get(v___x_710_, 8);
lean_inc_ref(v_infoState_711_);
lean_dec(v___x_710_);
v_enabled_712_ = lean_ctor_get_uint8(v_infoState_711_, sizeof(void*)*3);
lean_dec_ref(v_infoState_711_);
if (v_enabled_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_t_706_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_716_, 0, v_t_706_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_716_, v___y_708_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_722_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_731_ = l_Lean_stringToMessageData(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_737_ = l_Lean_stringToMessageData(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_744_, lean_object* v_declHint_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_env_750_; uint8_t v___x_751_; 
v___x_748_ = lean_box(0);
v___x_749_ = lean_st_ref_get(v___y_746_);
v_env_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_env_750_);
lean_dec(v___x_749_);
v___x_751_ = l_Lean_Name_isAnonymous(v_declHint_745_);
if (v___x_751_ == 0)
{
uint8_t v_isExporting_752_; 
v_isExporting_752_ = lean_ctor_get_uint8(v_env_750_, sizeof(void*)*13);
if (v_isExporting_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec_ref(v_env_750_);
lean_dec(v_declHint_745_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_msg_744_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
lean_inc_ref(v_env_750_);
v___x_754_ = l_Lean_Environment_setExporting(v_env_750_, v___x_751_);
lean_inc(v_declHint_745_);
lean_inc_ref(v___x_754_);
v___x_755_ = l_Lean_Environment_contains(v___x_754_, v_declHint_745_, v_isExporting_752_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v_env_750_);
lean_dec(v_declHint_745_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_msg_744_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_c_762_; lean_object* v___x_763_; 
v___x_757_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_758_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_759_ = l_Lean_Options_empty;
lean_inc_ref(v___x_754_);
v___x_760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_760_, 0, v___x_754_);
lean_ctor_set(v___x_760_, 1, v___x_757_);
lean_ctor_set(v___x_760_, 2, v___x_758_);
lean_ctor_set(v___x_760_, 3, v___x_759_);
lean_inc(v_declHint_745_);
v___x_761_ = l_Lean_MessageData_ofConstName(v_declHint_745_, v___x_751_);
v_c_762_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_762_, 0, v___x_760_);
lean_ctor_set(v_c_762_, 1, v___x_761_);
v___x_763_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_754_, v_declHint_745_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_env_750_);
lean_dec(v_declHint_745_);
v___x_764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_c_762_);
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_MessageData_note(v___x_767_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v_msg_744_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_805_; 
v_val_771_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_805_ == 0)
{
v___x_773_ = v___x_763_;
v_isShared_774_ = v_isSharedCheck_805_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v___x_763_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_805_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v_moduleNames_776_; lean_object* v_mod_777_; uint8_t v___x_778_; 
v___x_775_ = l_Lean_Environment_header(v_env_750_);
lean_dec_ref(v_env_750_);
v_moduleNames_776_ = lean_ctor_get(v___x_775_, 4);
lean_inc_ref(v_moduleNames_776_);
lean_dec_ref(v___x_775_);
v_mod_777_ = lean_array_get(v___x_748_, v_moduleNames_776_, v_val_771_);
lean_dec(v_val_771_);
lean_dec_ref(v_moduleNames_776_);
v___x_778_ = l_Lean_isPrivateName(v_declHint_745_);
lean_dec(v_declHint_745_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_c_762_);
v___x_781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_MessageData_ofName(v_mod_777_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_MessageData_note(v___x_786_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v_msg_744_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 0);
lean_ctor_set(v___x_773_, 0, v___x_788_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_c_762_);
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_MessageData_ofName(v_mod_777_);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_MessageData_note(v___x_799_);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v_msg_744_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 0);
lean_ctor_set(v___x_773_, 0, v___x_801_);
v___x_803_ = v___x_773_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v_env_750_);
lean_dec(v_declHint_745_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_msg_744_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_807_, lean_object* v_declHint_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_807_, v_declHint_808_, v___y_809_);
lean_dec(v___y_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_812_, lean_object* v_declHint_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_827_; 
v___x_817_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_812_, v_declHint_813_, v___y_815_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_827_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = l_Lean_unknownIdentifierMessageTag;
v___x_823_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_828_, lean_object* v_declHint_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_828_, v_declHint_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_toCold_839_; lean_object* v_currRecDepth_840_; lean_object* v_ref_841_; uint16_t v_optionFlags_842_; uint8_t v_suppressElabErrors_843_; uint8_t v_checkDeprecated_844_; uint8_t v_isRecordingDeps_845_; lean_object* v_ref_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_toCold_839_ = lean_ctor_get(v___y_836_, 0);
v_currRecDepth_840_ = lean_ctor_get(v___y_836_, 1);
v_ref_841_ = lean_ctor_get(v___y_836_, 2);
v_optionFlags_842_ = lean_ctor_get_uint16(v___y_836_, sizeof(void*)*3);
v_suppressElabErrors_843_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*3 + 2);
v_checkDeprecated_844_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*3 + 3);
v_isRecordingDeps_845_ = lean_ctor_get_uint8(v___y_836_, sizeof(void*)*3 + 4);
v_ref_846_ = l_Lean_replaceRef(v_ref_834_, v_ref_841_);
lean_inc(v_currRecDepth_840_);
lean_inc_ref(v_toCold_839_);
v___x_847_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_847_, 0, v_toCold_839_);
lean_ctor_set(v___x_847_, 1, v_currRecDepth_840_);
lean_ctor_set(v___x_847_, 2, v_ref_846_);
lean_ctor_set_uint16(v___x_847_, sizeof(void*)*3, v_optionFlags_842_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 2, v_suppressElabErrors_843_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 3, v_checkDeprecated_844_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 4, v_isRecordingDeps_845_);
v___x_848_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_835_, v___x_847_, v___y_837_);
lean_dec_ref_known(v___x_847_, 3);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_849_, lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_849_, v_msg_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v_ref_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_855_, lean_object* v_msg_856_, lean_object* v_declHint_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_863_; 
v___x_861_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_856_, v_declHint_857_, v___y_858_, v___y_859_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_855_, v_a_862_, v___y_858_, v___y_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_864_, lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_864_, v_msg_865_, v_declHint_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_ref_864_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_874_, lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_879_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_880_ = 0;
lean_inc(v_constName_875_);
v___x_881_ = l_Lean_MessageData_ofConstName(v_constName_875_, v___x_880_);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_879_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_874_, v___x_884_, v_constName_875_, v___y_876_, v___y_877_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_886_, lean_object* v_constName_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_886_, v_constName_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v_ref_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_ref_896_; lean_object* v___x_897_; 
v_ref_896_ = lean_ctor_get(v___y_893_, 2);
v___x_897_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_896_, v_constName_892_, v___y_893_, v___y_894_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_env_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
v___x_907_ = lean_st_ref_get(v___y_905_);
v_env_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_907_);
v___x_909_ = 0;
lean_inc(v_constName_903_);
v___x_910_ = l_Lean_Environment_findConstVal_x3f(v_env_908_, v_constName_903_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_903_, v___y_904_, v___y_905_);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_constName_903_);
v_val_912_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_910_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v___x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 0);
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_val_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v___x_927_; 
v___x_927_ = l_List_reverse___redArg(v_a_926_);
return v___x_927_;
}
else
{
lean_object* v_head_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_938_; 
v_head_928_ = lean_ctor_get(v_a_925_, 0);
v_tail_929_ = lean_ctor_get(v_a_925_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_938_ == 0)
{
v___x_931_ = v_a_925_;
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_head_928_);
lean_dec(v_a_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_938_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = l_Lean_mkLevelParam(v_head_928_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_a_926_);
lean_ctor_set(v___x_931_, 0, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_a_926_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
v_a_925_ = v_tail_929_;
v_a_926_ = v___x_935_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
lean_inc(v_constName_939_);
v___x_943_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_955_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_955_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_levelParams_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_levelParams_948_ = lean_ctor_get(v_a_944_, 1);
lean_inc(v_levelParams_948_);
lean_dec(v_a_944_);
v___x_949_ = lean_box(0);
v___x_950_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_948_, v___x_949_);
v___x_951_ = l_Lean_mkConst(v_constName_939_, v___x_950_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_951_);
v___x_953_ = v___x_946_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_constName_939_);
v_a_956_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_943_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_943_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_969_, lean_object* v_n_970_, lean_object* v_expectedType_x3f_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_970_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_stx_969_);
v___x_979_ = l_Lean_LocalContext_empty;
v___x_980_ = 0;
v___x_981_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v_expectedType_x3f_971_);
lean_ctor_set(v___x_981_, 3, v_a_976_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*4, v___x_980_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*4 + 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
v___x_983_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_982_, v___y_972_, v___y_973_);
return v___x_983_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_expectedType_x3f_971_);
lean_dec(v_stx_969_);
v_a_984_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_975_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_975_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_992_, lean_object* v_n_993_, lean_object* v_expectedType_x3f_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_992_, v_n_993_, v_expectedType_x3f_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0(lean_object* v___x_999_, lean_object* v_entry_1000_, lean_object* v_s_1001_){
_start:
{
lean_object* v_addEntryFn_1002_; lean_object* v_importedEntries_1003_; lean_object* v_state_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v_addEntryFn_1002_ = lean_ctor_get(v___x_999_, 3);
lean_inc(v_addEntryFn_1002_);
lean_dec_ref(v___x_999_);
v_importedEntries_1003_ = lean_ctor_get(v_s_1001_, 0);
v_state_1004_ = lean_ctor_get(v_s_1001_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_s_1001_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1006_ = v_s_1001_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_state_1004_);
lean_inc(v_importedEntries_1003_);
lean_dec(v_s_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_state_1008_; lean_object* v___x_1010_; 
v_state_1008_ = lean_apply_2(v_addEntryFn_1002_, v_state_1004_, v_entry_1000_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_state_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_importedEntries_1003_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_state_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_keys_1013_);
v___x_1017_ = lean_nat_dec_lt(v_i_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_i_1014_);
return v___x_1017_;
}
else
{
lean_object* v_k_x27_1018_; uint8_t v___x_1019_; 
v_k_x27_1018_ = lean_array_fget_borrowed(v_keys_1013_, v_i_1014_);
v___x_1019_ = l_Lean_instBEqExtraModUse_beq(v_k_1015_, v_k_x27_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1014_, v___x_1020_);
lean_dec(v_i_1014_);
v_i_1014_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_i_1014_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1023_, v_i_1024_, v_k_1025_);
lean_dec_ref(v_k_1025_);
lean_dec_ref(v_keys_1023_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1028_, size_t v_x_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_object* v_es_1031_; lean_object* v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v_j_1035_; lean_object* v___x_1036_; 
v_es_1031_ = lean_ctor_get(v_x_1028_, 0);
v___x_1032_ = lean_box(2);
v___x_1033_ = ((size_t)31ULL);
v___x_1034_ = lean_usize_land(v_x_1029_, v___x_1033_);
v_j_1035_ = lean_usize_to_nat(v___x_1034_);
v___x_1036_ = lean_array_get_borrowed(v___x_1032_, v_es_1031_, v_j_1035_);
lean_dec(v_j_1035_);
switch(lean_obj_tag(v___x_1036_))
{
case 0:
{
lean_object* v_key_1037_; uint8_t v___x_1038_; 
v_key_1037_ = lean_ctor_get(v___x_1036_, 0);
v___x_1038_ = l_Lean_instBEqExtraModUse_beq(v_x_1030_, v_key_1037_);
return v___x_1038_;
}
case 1:
{
lean_object* v_node_1039_; size_t v___x_1040_; size_t v___x_1041_; 
v_node_1039_ = lean_ctor_get(v___x_1036_, 0);
v___x_1040_ = ((size_t)5ULL);
v___x_1041_ = lean_usize_shift_right(v_x_1029_, v___x_1040_);
v_x_1028_ = v_node_1039_;
v_x_1029_ = v___x_1041_;
goto _start;
}
default: 
{
uint8_t v___x_1043_; 
v___x_1043_ = 0;
return v___x_1043_;
}
}
}
else
{
lean_object* v_ks_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_ks_1044_ = lean_ctor_get(v_x_1028_, 0);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1044_, v___x_1045_, v_x_1030_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
size_t v_x_6585__boxed_1050_; uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_x_6585__boxed_1050_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_res_1051_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1047_, v_x_6585__boxed_1050_, v_x_1049_);
lean_dec_ref(v_x_1049_);
lean_dec_ref(v_x_1047_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
uint64_t v___x_1055_; size_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1055_ = l_Lean_instHashableExtraModUse_hash(v_x_1054_);
v___x_1056_ = lean_uint64_to_usize(v___x_1055_);
v___x_1057_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1053_, v___x_1056_, v_x_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1058_, v_x_1059_);
lean_dec_ref(v_x_1059_);
lean_dec_ref(v_x_1058_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1062_; double v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_float_of_nat(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1119_; 
v_ref_1072_ = lean_ctor_get(v___y_1069_, 2);
v___x_1073_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1068_, v___y_1069_, v___y_1070_);
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1119_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1119_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v_traceState_1079_; lean_object* v_env_1080_; lean_object* v_nextMacroScope_1081_; lean_object* v_ngen_1082_; lean_object* v_auxDeclNGen_1083_; lean_object* v_cache_1084_; lean_object* v_recordedDeps_1085_; lean_object* v_messages_1086_; lean_object* v_infoState_1087_; lean_object* v_snapshotTasks_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1118_; 
v___x_1078_ = lean_st_ref_take(v___y_1070_);
v_traceState_1079_ = lean_ctor_get(v___x_1078_, 4);
v_env_1080_ = lean_ctor_get(v___x_1078_, 0);
v_nextMacroScope_1081_ = lean_ctor_get(v___x_1078_, 1);
v_ngen_1082_ = lean_ctor_get(v___x_1078_, 2);
v_auxDeclNGen_1083_ = lean_ctor_get(v___x_1078_, 3);
v_cache_1084_ = lean_ctor_get(v___x_1078_, 5);
v_recordedDeps_1085_ = lean_ctor_get(v___x_1078_, 6);
v_messages_1086_ = lean_ctor_get(v___x_1078_, 7);
v_infoState_1087_ = lean_ctor_get(v___x_1078_, 8);
v_snapshotTasks_1088_ = lean_ctor_get(v___x_1078_, 9);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1090_ = v___x_1078_;
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_snapshotTasks_1088_);
lean_inc(v_infoState_1087_);
lean_inc(v_messages_1086_);
lean_inc(v_recordedDeps_1085_);
lean_inc(v_cache_1084_);
lean_inc(v_traceState_1079_);
lean_inc(v_auxDeclNGen_1083_);
lean_inc(v_ngen_1082_);
lean_inc(v_nextMacroScope_1081_);
lean_inc(v_env_1080_);
lean_dec(v___x_1078_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint64_t v_tid_1092_; lean_object* v_traces_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1117_; 
v_tid_1092_ = lean_ctor_get_uint64(v_traceState_1079_, sizeof(void*)*1);
v_traces_1093_ = lean_ctor_get(v_traceState_1079_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_traceState_1079_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1095_ = v_traceState_1079_;
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_traces_1093_);
lean_dec(v_traceState_1079_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1117_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; double v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1100_ = 0;
v___x_1101_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1102_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1102_, 0, v_cls_1067_);
lean_ctor_set(v___x_1102_, 1, v___x_1098_);
lean_ctor_set(v___x_1102_, 2, v___x_1101_);
lean_ctor_set_float(v___x_1102_, sizeof(void*)*3, v___x_1099_);
lean_ctor_set_float(v___x_1102_, sizeof(void*)*3 + 8, v___x_1099_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*3 + 16, v___x_1100_);
v___x_1103_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1104_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v_a_1074_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
lean_inc(v_ref_1072_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_ref_1072_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_PersistentArray_push___redArg(v_traces_1093_, v___x_1105_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1106_);
v___x_1108_ = v___x_1095_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1106_);
lean_ctor_set_uint64(v_reuseFailAlloc_1116_, sizeof(void*)*1, v_tid_1092_);
v___x_1108_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v___x_1108_);
v___x_1110_ = v___x_1090_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_env_1080_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_nextMacroScope_1081_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_ngen_1082_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_auxDeclNGen_1083_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_cache_1084_);
lean_ctor_set(v_reuseFailAlloc_1115_, 6, v_recordedDeps_1085_);
lean_ctor_set(v_reuseFailAlloc_1115_, 7, v_messages_1086_);
lean_ctor_set(v_reuseFailAlloc_1115_, 8, v_infoState_1087_);
lean_ctor_set(v_reuseFailAlloc_1115_, 9, v_snapshotTasks_1088_);
v___x_1110_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_st_ref_put(v___y_1070_, v___x_1110_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1097_);
v___x_1113_ = v___x_1076_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1097_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1120_, lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1120_, v_msg_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1125_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1130_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v_cls_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_cls_1145_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1146_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1147_ = l_Lean_Name_append(v___x_1146_, v_cls_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1158_, uint8_t v_isMeta_1159_, lean_object* v_hint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_env_1182_; uint8_t v_isExporting_1183_; lean_object* v_entry_1184_; lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
v___x_1181_ = lean_st_ref_get(v___y_1162_);
v_env_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1181_);
v_isExporting_1183_ = lean_ctor_get_uint8(v_env_1182_, sizeof(void*)*13);
lean_dec_ref(v_env_1182_);
lean_inc(v_mod_1158_);
v_entry_1184_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1184_, 0, v_mod_1158_);
lean_ctor_set_uint8(v_entry_1184_, sizeof(void*)*1, v_isExporting_1183_);
lean_ctor_set_uint8(v_entry_1184_, sizeof(void*)*1 + 1, v_isMeta_1159_);
v___x_1185_ = lean_st_ref_get(v___y_1162_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1188_ = lean_box(1);
v___x_1189_ = lean_box(0);
v___x_1190_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1180_, v___x_1187_, v_env_1186_, v___x_1188_, v___x_1189_);
v___x_1191_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1190_, v_entry_1184_);
lean_dec(v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v_toCold_1192_; lean_object* v_options_1193_; lean_object* v_inheritedTraceOptions_1194_; uint8_t v_hasTrace_1195_; lean_object* v___f_1196_; uint8_t v___x_1197_; lean_object* v___y_1199_; 
v_toCold_1192_ = lean_ctor_get(v___y_1161_, 0);
v_options_1193_ = lean_ctor_get(v_toCold_1192_, 2);
v_inheritedTraceOptions_1194_ = lean_ctor_get(v_toCold_1192_, 11);
v_hasTrace_1195_ = lean_ctor_get_uint8(v_options_1193_, sizeof(void*)*1);
v___f_1196_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_1196_, 0, v___x_1187_);
lean_closure_set(v___f_1196_, 1, v_entry_1184_);
v___x_1197_ = 1;
if (v_hasTrace_1195_ == 0)
{
lean_dec(v_hint_1160_);
lean_dec(v_mod_1158_);
v___y_1199_ = v___y_1162_;
goto v___jp_1198_;
}
else
{
lean_object* v_cls_1217_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_cls_1217_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1237_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___x_1238_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1194_, v_options_1193_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_hint_1160_);
lean_dec(v_mod_1158_);
v___y_1199_ = v___y_1162_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1239_; lean_object* v___y_1241_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1183_ == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1241_ = v___x_1248_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1241_ = v___x_1249_;
goto v___jp_1240_;
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_inc_ref(v___y_1241_);
v___x_1242_ = l_Lean_stringToMessageData(v___y_1241_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1239_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
if (v_isMeta_1159_ == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1224_ = v___x_1245_;
v___y_1225_ = v___x_1246_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1247_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1224_ = v___x_1245_;
v___y_1225_ = v___x_1247_;
goto v___jp_1223_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1219_);
lean_ctor_set(v___x_1221_, 1, v___y_1220_);
v___x_1222_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1217_, v___x_1221_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_dec_ref_known(v___x_1222_, 1);
v___y_1199_ = v___y_1162_;
goto v___jp_1198_;
}
else
{
lean_dec_ref(v___f_1196_);
return v___x_1222_;
}
}
v___jp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
lean_inc_ref(v___y_1225_);
v___x_1226_ = l_Lean_stringToMessageData(v___y_1225_);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___y_1224_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_MessageData_ofName(v_mod_1158_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = l_Lean_Name_isAnonymous(v_hint_1160_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8);
v___x_1234_ = l_Lean_MessageData_ofName(v_hint_1160_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___y_1219_ = v___x_1231_;
v___y_1220_ = v___x_1235_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_hint_1160_);
v___x_1236_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___y_1219_ = v___x_1231_;
v___y_1220_ = v___x_1236_;
goto v___jp_1218_;
}
}
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v_toEnvExtension_1201_; lean_object* v_env_1202_; lean_object* v_nextMacroScope_1203_; lean_object* v_ngen_1204_; lean_object* v_auxDeclNGen_1205_; lean_object* v_traceState_1206_; lean_object* v_recordedDeps_1207_; lean_object* v_messages_1208_; lean_object* v_infoState_1209_; lean_object* v_snapshotTasks_1210_; lean_object* v_asyncMode_1211_; uint8_t v_logWrites_1212_; lean_object* v___x_1213_; 
v___x_1200_ = lean_st_ref_take(v___y_1199_);
v_toEnvExtension_1201_ = lean_ctor_get(v___x_1187_, 0);
v_env_1202_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_env_1202_);
v_nextMacroScope_1203_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_nextMacroScope_1203_);
v_ngen_1204_ = lean_ctor_get(v___x_1200_, 2);
lean_inc_ref(v_ngen_1204_);
v_auxDeclNGen_1205_ = lean_ctor_get(v___x_1200_, 3);
lean_inc_ref(v_auxDeclNGen_1205_);
v_traceState_1206_ = lean_ctor_get(v___x_1200_, 4);
lean_inc_ref(v_traceState_1206_);
v_recordedDeps_1207_ = lean_ctor_get(v___x_1200_, 6);
lean_inc_ref(v_recordedDeps_1207_);
v_messages_1208_ = lean_ctor_get(v___x_1200_, 7);
lean_inc_ref(v_messages_1208_);
v_infoState_1209_ = lean_ctor_get(v___x_1200_, 8);
lean_inc_ref(v_infoState_1209_);
v_snapshotTasks_1210_ = lean_ctor_get(v___x_1200_, 9);
lean_inc_ref(v_snapshotTasks_1210_);
lean_dec(v___x_1200_);
v_asyncMode_1211_ = lean_ctor_get(v_toEnvExtension_1201_, 2);
v_logWrites_1212_ = lean_ctor_get_uint8(v_toEnvExtension_1201_, sizeof(void*)*6);
v___x_1213_ = lean_box(0);
if (v_logWrites_1212_ == 0)
{
lean_object* v___x_1214_; 
lean_inc_ref(v_toEnvExtension_1201_);
v___x_1214_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1201_, v_env_1202_, v___f_1196_, v_asyncMode_1211_, v___x_1189_, v___x_1197_);
v___y_1165_ = v_recordedDeps_1207_;
v___y_1166_ = v_nextMacroScope_1203_;
v___y_1167_ = v_infoState_1209_;
v___y_1168_ = v___x_1213_;
v___y_1169_ = v___y_1199_;
v___y_1170_ = v_ngen_1204_;
v___y_1171_ = v_auxDeclNGen_1205_;
v___y_1172_ = v_messages_1208_;
v___y_1173_ = v_traceState_1206_;
v___y_1174_ = v_snapshotTasks_1210_;
v___y_1175_ = v___x_1214_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc_ref_n(v_toEnvExtension_1201_, 2);
v___x_1215_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1201_, v_env_1202_);
lean_dec_ref(v_env_1202_);
v___x_1216_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1201_, v___x_1215_, v___f_1196_, v_asyncMode_1211_, v___x_1189_, v___x_1197_);
v___y_1165_ = v_recordedDeps_1207_;
v___y_1166_ = v_nextMacroScope_1203_;
v___y_1167_ = v_infoState_1209_;
v___y_1168_ = v___x_1213_;
v___y_1169_ = v___y_1199_;
v___y_1170_ = v_ngen_1204_;
v___y_1171_ = v_auxDeclNGen_1205_;
v___y_1172_ = v_messages_1208_;
v___y_1173_ = v_traceState_1206_;
v___y_1174_ = v_snapshotTasks_1210_;
v___y_1175_ = v___x_1216_;
goto v___jp_1164_;
}
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref_known(v_entry_1184_, 1);
lean_dec(v_hint_1160_);
lean_dec(v_mod_1158_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
v___jp_1164_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1);
v___x_1177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1177_, 0, v___y_1175_);
lean_ctor_set(v___x_1177_, 1, v___y_1166_);
lean_ctor_set(v___x_1177_, 2, v___y_1170_);
lean_ctor_set(v___x_1177_, 3, v___y_1171_);
lean_ctor_set(v___x_1177_, 4, v___y_1173_);
lean_ctor_set(v___x_1177_, 5, v___x_1176_);
lean_ctor_set(v___x_1177_, 6, v___y_1165_);
lean_ctor_set(v___x_1177_, 7, v___y_1172_);
lean_ctor_set(v___x_1177_, 8, v___y_1167_);
lean_ctor_set(v___x_1177_, 9, v___y_1174_);
v___x_1178_ = lean_st_ref_put(v___y_1169_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1168_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1252_, lean_object* v_isMeta_1253_, lean_object* v_hint_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_isMeta_boxed_1258_; lean_object* v_res_1259_; 
v_isMeta_boxed_1258_ = lean_unbox(v_isMeta_1253_);
v_res_1259_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1252_, v_isMeta_boxed_1258_, v_hint_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1260_, lean_object* v_declName_1261_, lean_object* v_as_1262_, size_t v_sz_1263_, size_t v_i_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_lt(v_i_1264_, v_sz_1263_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec(v_declName_1261_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_b_1265_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v_modules_1272_; lean_object* v___x_1273_; lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v_toImport_1276_; lean_object* v_module_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1271_ = l_Lean_Environment_header(v___x_1260_);
v_modules_1272_ = lean_ctor_get(v___x_1271_, 3);
lean_inc_ref(v_modules_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1274_ = lean_array_uget_borrowed(v_as_1262_, v_i_1264_);
v___x_1275_ = lean_array_get(v___x_1273_, v_modules_1272_, v_a_1274_);
lean_dec_ref(v_modules_1272_);
v_toImport_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc_ref(v_toImport_1276_);
lean_dec(v___x_1275_);
v_module_1277_ = lean_ctor_get(v_toImport_1276_, 0);
lean_inc(v_module_1277_);
lean_dec_ref(v_toImport_1276_);
v___x_1278_ = lean_box(0);
v___x_1279_ = 0;
lean_inc(v_declName_1261_);
v___x_1280_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1277_, v___x_1279_, v_declName_1261_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1280_) == 0)
{
size_t v___x_1281_; size_t v___x_1282_; 
lean_dec_ref_known(v___x_1280_, 1);
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1264_, v___x_1281_);
v_i_1264_ = v___x_1282_;
v_b_1265_ = v___x_1278_;
goto _start;
}
else
{
lean_dec(v_declName_1261_);
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1284_, lean_object* v_declName_1285_, lean_object* v_as_1286_, lean_object* v_sz_1287_, lean_object* v_i_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
size_t v_sz_boxed_1293_; size_t v_i_boxed_1294_; lean_object* v_res_1295_; 
v_sz_boxed_1293_ = lean_unbox_usize(v_sz_1287_);
lean_dec(v_sz_1287_);
v_i_boxed_1294_ = lean_unbox_usize(v_i_1288_);
lean_dec(v_i_1288_);
v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1284_, v_declName_1285_, v_as_1286_, v_sz_boxed_1293_, v_i_boxed_1294_, v_b_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_as_1286_);
lean_dec_ref(v___x_1284_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_box(0);
return v___x_1298_;
}
else
{
lean_object* v_key_1299_; lean_object* v_value_1300_; lean_object* v_tail_1301_; uint8_t v___x_1302_; 
v_key_1299_ = lean_ctor_get(v_x_1297_, 0);
v_value_1300_ = lean_ctor_get(v_x_1297_, 1);
v_tail_1301_ = lean_ctor_get(v_x_1297_, 2);
v___x_1302_ = lean_name_eq(v_key_1299_, v_a_1296_);
if (v___x_1302_ == 0)
{
v_x_1297_ = v_tail_1301_;
goto _start;
}
else
{
lean_object* v___x_1304_; 
lean_inc(v_value_1300_);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_value_1300_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1305_, v_x_1306_);
lean_dec(v_x_1306_);
lean_dec(v_a_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_buckets_1310_; lean_object* v___x_1311_; uint64_t v___y_1313_; 
v_buckets_1310_ = lean_ctor_get(v_m_1308_, 1);
v___x_1311_ = lean_array_get_size(v_buckets_1310_);
if (lean_obj_tag(v_a_1309_) == 0)
{
uint64_t v___x_1327_; 
v___x_1327_ = 1723ULL;
v___y_1313_ = v___x_1327_;
goto v___jp_1312_;
}
else
{
uint64_t v_hash_1328_; 
v_hash_1328_ = lean_ctor_get_uint64(v_a_1309_, sizeof(void*)*2);
v___y_1313_ = v_hash_1328_;
goto v___jp_1312_;
}
v___jp_1312_:
{
uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v_fold_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1314_ = 32ULL;
v___x_1315_ = lean_uint64_shift_right(v___y_1313_, v___x_1314_);
v_fold_1316_ = lean_uint64_xor(v___y_1313_, v___x_1315_);
v___x_1317_ = 16ULL;
v___x_1318_ = lean_uint64_shift_right(v_fold_1316_, v___x_1317_);
v___x_1319_ = lean_uint64_xor(v_fold_1316_, v___x_1318_);
v___x_1320_ = lean_uint64_to_usize(v___x_1319_);
v___x_1321_ = lean_usize_of_nat(v___x_1311_);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_sub(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_usize_land(v___x_1320_, v___x_1323_);
v___x_1325_ = lean_array_uget_borrowed(v_buckets_1310_, v___x_1324_);
v___x_1326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1309_, v___x_1325_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_m_1329_);
return v_res_1331_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1335_, uint8_t v_isMeta_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_env_1345_; lean_object* v___y_1347_; lean_object* v___x_1360_; 
v___x_1340_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0);
v___x_1341_ = lean_st_ref_get(v___y_1338_);
v_env_1345_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref(v_env_1345_);
lean_dec(v___x_1341_);
v___x_1360_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1345_, v_declName_1335_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref(v_env_1345_);
lean_dec(v_declName_1335_);
goto v___jp_1342_;
}
else
{
lean_object* v_val_1361_; lean_object* v___x_1362_; lean_object* v_modules_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Environment_header(v_env_1345_);
v_modules_1363_ = lean_ctor_get(v___x_1362_, 3);
lean_inc_ref(v_modules_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = lean_array_get_size(v_modules_1363_);
v___x_1365_ = lean_nat_dec_lt(v_val_1361_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v_modules_1363_);
lean_dec(v_val_1361_);
lean_dec_ref(v_env_1345_);
lean_dec(v_declName_1335_);
goto v___jp_1342_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___y_1369_; 
v___x_1366_ = lean_array_fget(v_modules_1363_, v_val_1361_);
lean_dec(v_val_1361_);
lean_dec_ref(v_modules_1363_);
v___x_1367_ = lean_st_ref_get(v___y_1338_);
if (v_isMeta_1336_ == 0)
{
lean_dec(v___x_1367_);
v___y_1369_ = v_isMeta_1336_;
goto v___jp_1368_;
}
else
{
lean_object* v_env_1380_; uint8_t v___x_1381_; 
v_env_1380_ = lean_ctor_get(v___x_1367_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1367_);
lean_inc(v_declName_1335_);
v___x_1381_ = l_Lean_isMarkedMeta(v_env_1380_, v_declName_1335_);
if (v___x_1381_ == 0)
{
v___y_1369_ = v_isMeta_1336_;
goto v___jp_1368_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = 0;
v___y_1369_ = v___x_1382_;
goto v___jp_1368_;
}
}
v___jp_1368_:
{
lean_object* v_toImport_1370_; lean_object* v_module_1371_; lean_object* v___x_1372_; 
v_toImport_1370_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_ref(v_toImport_1370_);
lean_dec(v___x_1366_);
v_module_1371_ = lean_ctor_get(v_toImport_1370_, 0);
lean_inc(v_module_1371_);
lean_dec_ref(v_toImport_1370_);
lean_inc(v_declName_1335_);
v___x_1372_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1371_, v___y_1369_, v_declName_1335_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1372_, 1);
v___x_1373_ = l_Lean_indirectModUseExt;
v___x_1374_ = lean_box(1);
v___x_1375_ = lean_box(0);
lean_inc_ref(v_env_1345_);
v___x_1376_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1340_, v___x_1373_, v_env_1345_, v___x_1374_, v___x_1375_);
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1376_, v_declName_1335_);
lean_dec(v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___y_1347_ = v___x_1378_;
goto v___jp_1346_;
}
else
{
lean_object* v_val_1379_; 
v_val_1379_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v___x_1377_, 1);
v___y_1347_ = v_val_1379_;
goto v___jp_1346_;
}
}
else
{
lean_dec_ref(v_env_1345_);
lean_dec(v_declName_1335_);
return v___x_1372_;
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = lean_box(0);
v_sz_1349_ = lean_array_size(v___y_1347_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1345_, v_declName_1335_, v___y_1347_, v_sz_1349_, v___x_1350_, v___x_1348_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v_env_1345_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1351_, 0);
lean_dec(v_unused_1359_);
v___x_1353_ = v___x_1351_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v___x_1351_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1348_);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1348_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1383_, lean_object* v_isMeta_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v_isMeta_boxed_1388_; lean_object* v_res_1389_; 
v_isMeta_boxed_1388_ = lean_unbox(v_isMeta_1384_);
v_res_1389_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1383_, v_isMeta_boxed_1388_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1390_, uint8_t v_x_1391_, lean_object* v_stx_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
lean_inc(v_stx_1392_);
v___x_1396_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1390_, v_stx_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1449_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1449_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1449_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v_env_1402_; uint8_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1401_ = lean_st_ref_get(v___y_1394_);
v_env_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc_ref(v_env_1402_);
lean_dec(v___x_1401_);
v___x_1403_ = 1;
lean_inc(v_a_1397_);
v___x_1404_ = l_Lean_Environment_contains(v_env_1402_, v_a_1397_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; 
lean_dec(v_stx_1392_);
if (v_isShared_1400_ == 0)
{
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1397_);
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
uint8_t v___x_1408_; lean_object* v___x_1409_; 
lean_del_object(v___x_1399_);
v___x_1408_ = 0;
lean_inc(v_a_1397_);
v___x_1409_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1397_, v___x_1408_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1440_);
v___x_1411_ = v___x_1409_;
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v___x_1409_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v_infoState_1414_; uint8_t v_enabled_1415_; 
v___x_1413_ = lean_st_ref_get(v___y_1394_);
v_infoState_1414_ = lean_ctor_get(v___x_1413_, 8);
lean_inc_ref(v_infoState_1414_);
lean_dec(v___x_1413_);
v_enabled_1415_ = lean_ctor_get_uint8(v_infoState_1414_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1414_);
if (v_enabled_1415_ == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_stx_1392_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v_a_1397_);
v___x_1417_ = v___x_1411_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1397_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1411_);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = l_Lean_Syntax_getArg(v_stx_1392_, v___x_1419_);
lean_dec(v_stx_1392_);
v___x_1421_ = lean_box(0);
lean_inc(v_a_1397_);
v___x_1422_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1420_, v_a_1397_, v___x_1421_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_a_1397_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1397_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1397_);
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1422_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1422_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1397_);
lean_dec(v_stx_1392_);
v_a_1441_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1409_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1409_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1392_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1450_, lean_object* v_x_1451_, lean_object* v_stx_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v_x_7163__boxed_1456_; lean_object* v_res_1457_; 
v_x_7163__boxed_1456_ = lean_unbox(v_x_1451_);
v_res_1457_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1450_, v_x_7163__boxed_1456_, v_stx_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1460_, lean_object* v_attrName_1461_, lean_object* v_parserNamespace_1462_, lean_object* v_typeName_1463_, lean_object* v_kind_1464_, lean_object* v_attrDeclName_1465_){
_start:
{
lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___f_1467_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1468_, 0, v_parserNamespace_1462_);
v___x_1469_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1470_ = lean_string_append(v_kind_1464_, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1471_, 0, v_attrBuiltinName_1460_);
lean_ctor_set(v___x_1471_, 1, v_attrName_1461_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
lean_ctor_set(v___x_1471_, 3, v_typeName_1463_);
lean_ctor_set(v___x_1471_, 4, v___f_1468_);
lean_ctor_set(v___x_1471_, 5, v___f_1467_);
v___x_1472_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1471_, v_attrDeclName_1465_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1473_, lean_object* v_attrName_1474_, lean_object* v_parserNamespace_1475_, lean_object* v_typeName_1476_, lean_object* v_kind_1477_, lean_object* v_attrDeclName_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1473_, v_attrName_1474_, v_parserNamespace_1475_, v_typeName_1476_, v_kind_1477_, v_attrDeclName_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1481_, lean_object* v_attrBuiltinName_1482_, lean_object* v_attrName_1483_, lean_object* v_parserNamespace_1484_, lean_object* v_typeName_1485_, lean_object* v_kind_1486_, lean_object* v_attrDeclName_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1482_, v_attrName_1483_, v_parserNamespace_1484_, v_typeName_1485_, v_kind_1486_, v_attrDeclName_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1490_, lean_object* v_attrBuiltinName_1491_, lean_object* v_attrName_1492_, lean_object* v_parserNamespace_1493_, lean_object* v_typeName_1494_, lean_object* v_kind_1495_, lean_object* v_attrDeclName_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1490_, v_attrBuiltinName_1491_, v_attrName_1492_, v_parserNamespace_1493_, v_typeName_1494_, v_kind_1495_, v_attrDeclName_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1499_, lean_object* v_m_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1500_, v_a_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1503_, lean_object* v_m_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1503_, v_m_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec_ref(v_m_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1507_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1518_, v_x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
uint8_t v_res_1524_; lean_object* v_r_1525_; 
v_res_1524_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1521_, v_x_1522_, v_x_1523_);
lean_dec_ref(v_x_1523_);
lean_dec_ref(v_x_1522_);
v_r_1525_ = lean_box(v_res_1524_);
return v_r_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1526_, lean_object* v_a_1527_, lean_object* v_x_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1527_, v_x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1530_, lean_object* v_a_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1530_, v_a_1531_, v_x_1532_);
lean_dec(v_x_1532_);
lean_dec(v_a_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1534_, lean_object* v_x_1535_, size_t v_x_1536_, lean_object* v_x_1537_){
_start:
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1535_, v_x_1536_, v_x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1539_, lean_object* v_x_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
size_t v_x_7333__boxed_1543_; uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_x_7333__boxed_1543_ = lean_unbox_usize(v_x_1541_);
lean_dec(v_x_1541_);
v_res_1544_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1539_, v_x_1540_, v_x_7333__boxed_1543_, v_x_1542_);
lean_dec_ref(v_x_1542_);
lean_dec_ref(v_x_1540_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1546_, lean_object* v_constName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1547_, v___y_1548_, v___y_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_constName_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1552_, v_constName_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1558_, lean_object* v_keys_1559_, lean_object* v_vals_1560_, lean_object* v_heq_1561_, lean_object* v_i_1562_, lean_object* v_k_1563_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1559_, v_i_1562_, v_k_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1565_, lean_object* v_keys_1566_, lean_object* v_vals_1567_, lean_object* v_heq_1568_, lean_object* v_i_1569_, lean_object* v_k_1570_){
_start:
{
uint8_t v_res_1571_; lean_object* v_r_1572_; 
v_res_1571_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1565_, v_keys_1566_, v_vals_1567_, v_heq_1568_, v_i_1569_, v_k_1570_);
lean_dec_ref(v_k_1570_);
lean_dec_ref(v_vals_1567_);
lean_dec_ref(v_keys_1566_);
v_r_1572_ = lean_box(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1573_, lean_object* v_ref_1574_, lean_object* v_constName_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1574_, v_constName_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_ref_1581_, lean_object* v_constName_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1580_, v_ref_1581_, v_constName_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v_ref_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1587_, lean_object* v_ref_1588_, lean_object* v_msg_1589_, lean_object* v_declHint_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1588_, v_msg_1589_, v_declHint_1590_, v___y_1591_, v___y_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_ref_1596_, lean_object* v_msg_1597_, lean_object* v_declHint_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1595_, v_ref_1596_, v_msg_1597_, v_declHint_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v_ref_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1603_, lean_object* v_declHint_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1603_, v_declHint_1604_, v___y_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1609_, lean_object* v_declHint_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1609_, v_declHint_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1615_, lean_object* v_ref_1616_, lean_object* v_msg_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1616_, v_msg_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_ref_1623_, lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1622_, v_ref_1623_, v_msg_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v_ref_1623_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1642_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1643_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1644_ = lean_box(0);
v___x_1645_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1646_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1641_, v___x_1643_, v___x_1644_, v___x_1645_, v___x_1642_, v_ref_1639_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1657_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1663_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1664_ = l_Lean_addBuiltinDocString(v___x_1662_, v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1695_ = l_Lean_addBuiltinDeclarationRanges(v___x_1693_, v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1698_, lean_object* v_a_1699_, lean_object* v_____r_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_declName_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1714_; 
v_declName_1703_ = lean_ctor_get(v_toOLeanEntry_1698_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_toOLeanEntry_1698_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_toOLeanEntry_1698_, 0);
lean_dec(v_unused_1715_);
v___x_1705_ = v_toOLeanEntry_1698_;
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_declName_1703_);
lean_dec(v_toOLeanEntry_1698_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1699_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v___x_1707_);
lean_ctor_set(v___x_1705_, 0, v_declName_1703_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_declName_1703_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v___y_1702_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1716_, lean_object* v_a_1717_, lean_object* v_____r_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1716_, v_a_1717_, v_____r_1718_, v___y_1719_, v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1725_, lean_object* v_as_x27_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
if (lean_obj_tag(v_as_x27_1726_) == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_stx_1725_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_b_1727_);
lean_ctor_set(v___x_1730_, 1, v___y_1729_);
return v___x_1730_;
}
else
{
lean_object* v_head_1731_; lean_object* v_tail_1732_; lean_object* v_toOLeanEntry_1733_; uint8_t v_isBuiltin_1734_; lean_object* v_value_1735_; lean_object* v_macroScope_1736_; lean_object* v_traceMsgs_1737_; lean_object* v_expandedMacroDecls_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_b_1727_);
v_head_1731_ = lean_ctor_get(v_as_x27_1726_, 0);
v_tail_1732_ = lean_ctor_get(v_as_x27_1726_, 1);
v_toOLeanEntry_1733_ = lean_ctor_get(v_head_1731_, 0);
v_isBuiltin_1734_ = lean_ctor_get_uint8(v_head_1731_, sizeof(void*)*2);
v_value_1735_ = lean_ctor_get(v_head_1731_, 1);
v_macroScope_1736_ = lean_ctor_get(v___y_1729_, 0);
v_traceMsgs_1737_ = lean_ctor_get(v___y_1729_, 1);
v_expandedMacroDecls_1738_ = lean_ctor_get(v___y_1729_, 2);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___y_1729_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1740_ = v___y_1729_;
v_isShared_1741_ = v_isSharedCheck_1803_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_expandedMacroDecls_1738_);
lean_inc(v_traceMsgs_1737_);
lean_inc(v_macroScope_1736_);
lean_dec(v___y_1729_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1803_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_methods_1742_; lean_object* v_quotContext_1743_; lean_object* v_currRecDepth_1744_; lean_object* v_maxRecDepth_1745_; lean_object* v_ref_1746_; lean_object* v___x_1747_; lean_object* v_a_1749_; lean_object* v_a_1750_; lean_object* v___x_1754_; lean_object* v_a_1756_; lean_object* v_a_1757_; lean_object* v___y_1764_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v_methods_1742_ = lean_ctor_get(v___y_1728_, 0);
v_quotContext_1743_ = lean_ctor_get(v___y_1728_, 1);
v_currRecDepth_1744_ = lean_ctor_get(v___y_1728_, 3);
v_maxRecDepth_1745_ = lean_ctor_get(v___y_1728_, 4);
v_ref_1746_ = lean_ctor_get(v___y_1728_, 5);
v___x_1747_ = lean_box(0);
v___x_1754_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_add(v_macroScope_1736_, v___x_1770_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1771_);
v___x_1773_ = v___x_1740_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_traceMsgs_1737_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_expandedMacroDecls_1738_);
v___x_1773_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1772_;
}
v___jp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_a_1749_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___x_1747_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v_a_1750_);
return v___x_1753_;
}
v___jp_1755_:
{
if (lean_obj_tag(v_a_1756_) == 1)
{
v_as_x27_1726_ = v_tail_1732_;
v_b_1727_ = v___x_1754_;
v___y_1729_ = v_a_1757_;
goto _start;
}
else
{
lean_object* v_declName_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v_stx_1725_);
v_declName_1759_ = lean_ctor_get(v_toOLeanEntry_1733_, 1);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_a_1756_);
lean_inc(v_declName_1759_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_declName_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
v_a_1749_ = v___x_1762_;
v_a_1750_ = v_a_1757_;
goto v___jp_1748_;
}
}
v___jp_1763_:
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v___y_1764_, 0);
if (lean_obj_tag(v_a_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_a_1767_; 
lean_inc_ref(v_a_1765_);
lean_dec(v_stx_1725_);
v_a_1766_ = lean_ctor_get(v___y_1764_, 1);
lean_inc(v_a_1766_);
lean_dec_ref(v___y_1764_);
v_a_1767_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v_a_1765_, 1);
v_a_1749_ = v_a_1767_;
v_a_1750_ = v_a_1766_;
goto v___jp_1748_;
}
else
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___y_1764_, 1);
lean_inc(v_a_1768_);
lean_dec_ref(v___y_1764_);
v_as_x27_1726_ = v_tail_1732_;
v_b_1727_ = v___x_1754_;
v___y_1729_ = v_a_1768_;
goto _start;
}
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc(v_ref_1746_);
lean_inc(v_maxRecDepth_1745_);
lean_inc(v_currRecDepth_1744_);
lean_inc(v_quotContext_1743_);
lean_inc(v_methods_1742_);
v___x_1774_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1774_, 0, v_methods_1742_);
lean_ctor_set(v___x_1774_, 1, v_quotContext_1743_);
lean_ctor_set(v___x_1774_, 2, v_macroScope_1736_);
lean_ctor_set(v___x_1774_, 3, v_currRecDepth_1744_);
lean_ctor_set(v___x_1774_, 4, v_maxRecDepth_1745_);
lean_ctor_set(v___x_1774_, 5, v_ref_1746_);
lean_inc(v_value_1735_);
lean_inc(v_stx_1725_);
v___x_1775_ = lean_apply_3(v_value_1735_, v_stx_1725_, v___x_1774_, v___x_1773_);
if (lean_obj_tag(v___x_1775_) == 0)
{
if (v_isBuiltin_1734_ == 0)
{
lean_object* v_a_1776_; lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1796_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 1);
v_a_1777_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1779_ = v___x_1775_;
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1776_);
lean_inc(v_a_1777_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_macroScope_1781_; lean_object* v_traceMsgs_1782_; lean_object* v_expandedMacroDecls_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1795_; 
v_macroScope_1781_ = lean_ctor_get(v_a_1776_, 0);
v_traceMsgs_1782_ = lean_ctor_get(v_a_1776_, 1);
v_expandedMacroDecls_1783_ = lean_ctor_get(v_a_1776_, 2);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1785_ = v_a_1776_;
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_expandedMacroDecls_1783_);
lean_inc(v_traceMsgs_1782_);
lean_inc(v_macroScope_1781_);
lean_dec(v_a_1776_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_declName_1787_; lean_object* v___x_1789_; 
v_declName_1787_ = lean_ctor_get(v_toOLeanEntry_1733_, 1);
lean_inc(v_declName_1787_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 1);
lean_ctor_set(v___x_1779_, 1, v_expandedMacroDecls_1783_);
lean_ctor_set(v___x_1779_, 0, v_declName_1787_);
v___x_1789_ = v___x_1779_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_declName_1787_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_expandedMacroDecls_1783_);
v___x_1789_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 2, v___x_1789_);
v___x_1791_ = v___x_1785_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_macroScope_1781_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_traceMsgs_1782_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; 
lean_inc_ref(v_toOLeanEntry_1733_);
v___x_1792_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1733_, v_a_1777_, v___x_1747_, v___y_1728_, v___x_1791_);
v___y_1764_ = v___x_1792_;
goto v___jp_1763_;
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1797_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1797_);
v_a_1798_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1775_, 2);
lean_inc_ref(v_toOLeanEntry_1733_);
v___x_1799_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1733_, v_a_1797_, v___x_1747_, v___y_1728_, v_a_1798_);
v___y_1764_ = v___x_1799_;
goto v___jp_1763_;
}
}
else
{
lean_object* v_a_1800_; lean_object* v_a_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1800_);
v_a_1801_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1775_, 2);
v_a_1756_ = v_a_1800_;
v_a_1757_ = v_a_1801_;
goto v___jp_1755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1804_, lean_object* v_as_x27_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1804_, v_as_x27_1805_, v_b_1806_, v___y_1807_, v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v_as_x27_1805_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1810_, lean_object* v_stx_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_a_1820_; lean_object* v_fst_1821_; 
v___x_1814_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1811_);
v___x_1815_ = l_Lean_Syntax_getKind(v_stx_1811_);
v___x_1816_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1814_, v_env_1810_, v___x_1815_);
lean_dec(v___x_1815_);
v___x_1817_ = lean_box(0);
v___x_1818_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1819_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1811_, v___x_1816_, v___x_1818_, v_a_1812_, v_a_1813_);
lean_dec(v___x_1816_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_fst_1821_ = lean_ctor_get(v_a_1820_, 0);
if (lean_obj_tag(v_fst_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1819_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1830_);
v___x_1824_ = v___x_1819_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1817_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
lean_inc_ref(v_fst_1821_);
v_a_1831_ = lean_ctor_get(v___x_1819_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1840_);
v___x_1833_ = v___x_1819_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1819_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_val_1835_; lean_object* v___x_1837_; 
v_val_1835_ = lean_ctor_get(v_fst_1821_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_fst_1821_, 1);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v_val_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_val_1835_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1831_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1841_, lean_object* v_stx_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1841_, v_stx_1842_, v_a_1843_, v_a_1844_);
lean_dec_ref(v_a_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1846_, lean_object* v_as_1847_, lean_object* v_as_x27_1848_, lean_object* v_b_1849_, lean_object* v_a_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1846_, v_as_x27_1848_, v_b_1849_, v___y_1851_, v___y_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1854_, lean_object* v_as_1855_, lean_object* v_as_x27_1856_, lean_object* v_b_1857_, lean_object* v_a_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1854_, v_as_1855_, v_as_x27_1856_, v_b_1857_, v_a_1858_, v___y_1859_, v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_as_x27_1856_);
lean_dec(v_as_1855_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1862_, lean_object* v_inst_1863_, lean_object* v_s_1864_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_apply_1(v_setNextMacroScope_1862_, v_s_1864_);
v___x_1866_ = lean_apply_2(v_inst_1863_, lean_box(0), v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_){
_start:
{
lean_object* v_getNextMacroScope_1870_; lean_object* v_setNextMacroScope_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
v_getNextMacroScope_1870_ = lean_ctor_get(v_inst_1869_, 1);
v_setNextMacroScope_1871_ = lean_ctor_get(v_inst_1869_, 2);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_inst_1869_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v_inst_1869_, 0);
lean_dec(v_unused_1881_);
v___x_1873_ = v_inst_1869_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_setNextMacroScope_1871_);
lean_inc(v_getNextMacroScope_1870_);
lean_dec(v_inst_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_inc(v_inst_1867_);
v___f_1875_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1875_, 0, v_setNextMacroScope_1871_);
lean_closure_set(v___f_1875_, 1, v_inst_1867_);
v___x_1876_ = lean_apply_2(v_inst_1867_, lean_box(0), v_getNextMacroScope_1870_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 2, v___f_1875_);
lean_ctor_set(v___x_1873_, 1, v___x_1876_);
lean_ctor_set(v___x_1873_, 0, v_inst_1868_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_inst_1868_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v___f_1875_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1882_, lean_object* v_n_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_){
_start:
{
lean_object* v_getNextMacroScope_1887_; lean_object* v_setNextMacroScope_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1897_; 
v_getNextMacroScope_1887_ = lean_ctor_get(v_inst_1886_, 1);
v_setNextMacroScope_1888_ = lean_ctor_get(v_inst_1886_, 2);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_inst_1886_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_inst_1886_, 0);
lean_dec(v_unused_1898_);
v___x_1890_ = v_inst_1886_;
v_isShared_1891_ = v_isSharedCheck_1897_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_setNextMacroScope_1888_);
lean_inc(v_getNextMacroScope_1887_);
lean_dec(v_inst_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1897_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_inc(v_inst_1884_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1892_, 0, v_setNextMacroScope_1888_);
lean_closure_set(v___f_1892_, 1, v_inst_1884_);
v___x_1893_ = lean_apply_2(v_inst_1884_, lean_box(0), v_getNextMacroScope_1887_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 2, v___f_1892_);
lean_ctor_set(v___x_1890_, 1, v___x_1893_);
lean_ctor_set(v___x_1890_, 0, v_inst_1885_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_inst_1885_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___f_1892_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0(lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v_nextMacroScope_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_st_ref_get(v___y_1900_);
v_nextMacroScope_1903_ = lean_ctor_get(v___x_1902_, 1);
lean_inc(v_nextMacroScope_1903_);
lean_dec(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_nextMacroScope_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0___boxed(lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Elab_instMonadMacroAdapterCoreM___lam__0(v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1(lean_object* v_next_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v_env_1914_; lean_object* v_ngen_1915_; lean_object* v_auxDeclNGen_1916_; lean_object* v_traceState_1917_; lean_object* v_cache_1918_; lean_object* v_recordedDeps_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1932_; 
v___x_1913_ = lean_st_ref_take(v___y_1911_);
v_env_1914_ = lean_ctor_get(v___x_1913_, 0);
v_ngen_1915_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1916_ = lean_ctor_get(v___x_1913_, 3);
v_traceState_1917_ = lean_ctor_get(v___x_1913_, 4);
v_cache_1918_ = lean_ctor_get(v___x_1913_, 5);
v_recordedDeps_1919_ = lean_ctor_get(v___x_1913_, 6);
v_messages_1920_ = lean_ctor_get(v___x_1913_, 7);
v_infoState_1921_ = lean_ctor_get(v___x_1913_, 8);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1913_, 9);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1913_, 1);
lean_dec(v_unused_1933_);
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_recordedDeps_1919_);
lean_inc(v_cache_1918_);
lean_inc(v_traceState_1917_);
lean_inc(v_auxDeclNGen_1916_);
lean_inc(v_ngen_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1932_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v_next_1909_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_env_1914_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_next_1909_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_ngen_1915_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_auxDeclNGen_1916_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_traceState_1917_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v_cache_1918_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_recordedDeps_1919_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 8, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 9, v_snapshotTasks_1922_);
v___x_1928_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_st_ref_put(v___y_1911_, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1926_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1___boxed(lean_object* v_next_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_instMonadMacroAdapterCoreM___lam__1(v_next_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2(void){
_start:
{
lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___f_1941_ = ((lean_object*)(l_Lean_Elab_instMonadMacroAdapterCoreM___closed__1));
v___f_1942_ = ((lean_object*)(l_Lean_Elab_instMonadMacroAdapterCoreM___closed__0));
v___x_1943_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___f_1942_);
lean_ctor_set(v___x_1944_, 2, v___f_1941_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Elab_instMonadMacroAdapterCoreM(void){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_obj_once(&l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2, &l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2_once, _init_l_Lean_Elab_instMonadMacroAdapterCoreM___closed__2);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1946_, lean_object* v_fst_1947_, lean_object* v_____do__lift_1948_, lean_object* v_____do__lift_1949_){
_start:
{
uint8_t v_hasTrace_1950_; 
v_hasTrace_1950_ = lean_ctor_get_uint8(v_____do__lift_1949_, sizeof(void*)*1);
if (v_hasTrace_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_fst_1947_);
v___x_1951_ = lean_box(v_hasTrace_1950_);
v___x_1952_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1951_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1953_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1954_ = l_Lean_Name_append(v___x_1953_, v_fst_1947_);
v___x_1955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1948_, v_____do__lift_1949_, v___x_1954_);
lean_dec(v___x_1954_);
v___x_1956_ = lean_box(v___x_1955_);
v___x_1957_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1956_);
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1958_, lean_object* v_fst_1959_, lean_object* v_____do__lift_1960_, lean_object* v_____do__lift_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1958_, v_fst_1959_, v_____do__lift_1960_, v_____do__lift_1961_);
lean_dec_ref(v_____do__lift_1961_);
lean_dec_ref(v_____do__lift_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_inst_1963_, lean_object* v_toPure_1964_, lean_object* v_fst_1965_, lean_object* v_toBind_1966_, lean_object* v_____do__lift_1967_){
_start:
{
lean_object* v_getOptionsUnrestricted_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; 
v_getOptionsUnrestricted_1968_ = lean_ctor_get(v_inst_1963_, 1);
lean_inc(v_getOptionsUnrestricted_1968_);
lean_dec_ref(v_inst_1963_);
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1969_, 0, v_toPure_1964_);
lean_closure_set(v___f_1969_, 1, v_fst_1965_);
lean_closure_set(v___f_1969_, 2, v_____do__lift_1967_);
v___x_1970_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1968_, v___f_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1971_, lean_object* v_snd_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_toMonadRef_1975_, lean_object* v_inst_1976_, lean_object* v_fst_1977_, uint8_t v_____do__lift_1978_){
_start:
{
if (v_____do__lift_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_fst_1977_);
lean_dec(v_inst_1976_);
lean_dec_ref(v_toMonadRef_1975_);
lean_dec_ref(v_inst_1974_);
lean_dec_ref(v_inst_1973_);
lean_dec_ref(v_snd_1972_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_apply_2(v_toPure_1971_, lean_box(0), v___x_1979_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v_toPure_1971_);
v___x_1981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_snd_1972_);
v___x_1982_ = l_Lean_MessageData_ofFormat(v___x_1981_);
v___x_1983_ = l_Lean_addTrace___redArg(v_inst_1973_, v_inst_1974_, v_toMonadRef_1975_, v_inst_1976_, v_fst_1977_, v___x_1982_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object* v_toPure_1984_, lean_object* v_snd_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_toMonadRef_1988_, lean_object* v_inst_1989_, lean_object* v_fst_1990_, lean_object* v_____do__lift_1991_){
_start:
{
uint8_t v_____do__lift_1464__boxed_1992_; lean_object* v_res_1993_; 
v_____do__lift_1464__boxed_1992_ = lean_unbox(v_____do__lift_1991_);
v_res_1993_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_toPure_1984_, v_snd_1985_, v_inst_1986_, v_inst_1987_, v_toMonadRef_1988_, v_inst_1989_, v_fst_1990_, v_____do__lift_1464__boxed_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_toPure_1996_, lean_object* v_toBind_1997_, lean_object* v_inst_1998_, lean_object* v_toMonadRef_1999_, lean_object* v_inst_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v_getInheritedTraceOptions_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_fst_2002_ = lean_ctor_get(v_x_2001_, 0);
lean_inc_n(v_fst_2002_, 2);
v_snd_2003_ = lean_ctor_get(v_x_2001_, 1);
lean_inc(v_snd_2003_);
lean_dec_ref(v_x_2001_);
v_getInheritedTraceOptions_2004_ = lean_ctor_get(v_inst_1994_, 2);
lean_inc(v_getInheritedTraceOptions_2004_);
lean_inc_n(v_toBind_1997_, 2);
lean_inc(v_toPure_1996_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2005_, 0, v_inst_1995_);
lean_closure_set(v___f_2005_, 1, v_toPure_1996_);
lean_closure_set(v___f_2005_, 2, v_fst_2002_);
lean_closure_set(v___f_2005_, 3, v_toBind_1997_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2006_, 0, v_toPure_1996_);
lean_closure_set(v___f_2006_, 1, v_snd_2003_);
lean_closure_set(v___f_2006_, 2, v_inst_1998_);
lean_closure_set(v___f_2006_, 3, v_inst_1994_);
lean_closure_set(v___f_2006_, 4, v_toMonadRef_1999_);
lean_closure_set(v___f_2006_, 5, v_inst_2000_);
lean_closure_set(v___f_2006_, 6, v_fst_2002_);
v___x_2007_ = lean_apply_4(v_toBind_1997_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2004_, v___f_2005_);
v___x_2008_ = lean_apply_4(v_toBind_1997_, lean_box(0), lean_box(0), v___x_2007_, v___f_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_2009_, lean_object* v___x_2010_, lean_object* v___x_2011_, lean_object* v_stx_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2009_, v_stx_2012_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
if (lean_obj_tag(v_a_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v___x_2011_);
lean_dec_ref(v___x_2010_);
v_a_2017_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2026_);
v___x_2019_ = v___x_2015_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_box(0);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_2017_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v_val_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2057_; 
v_val_2027_ = lean_ctor_get(v_a_2016_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_2016_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2029_ = v_a_2016_;
v_isShared_2030_ = v_isSharedCheck_2057_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_val_2027_);
lean_dec(v_a_2016_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2057_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_snd_2031_; 
v_snd_2031_ = lean_ctor_get(v_val_2027_, 1);
lean_inc(v_snd_2031_);
lean_dec(v_val_2027_);
if (lean_obj_tag(v_snd_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2042_; 
lean_del_object(v___x_2029_);
v_a_2032_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2015_, 2);
v_a_2033_ = lean_ctor_get(v_snd_2031_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_snd_2031_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2035_ = v_snd_2031_;
v_isShared_2036_ = v_isSharedCheck_2042_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v_snd_2031_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2042_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_1206__overap_2039_; lean_object* v___x_2040_; 
v___x_1206__overap_2039_ = l_liftExcept___redArg(v___x_2010_, v___x_2011_, v___x_2038_);
lean_inc_ref(v___y_2013_);
v___x_2040_ = lean_apply_2(v___x_1206__overap_2039_, v___y_2013_, v_a_2032_);
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2056_; 
v_a_2043_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2015_, 2);
v_a_2044_ = lean_ctor_get(v_snd_2031_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_2031_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2046_ = v_snd_2031_;
v_isShared_2047_ = v_isSharedCheck_2056_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v_snd_2031_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2056_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v_a_2044_);
v___x_2049_ = v___x_2029_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2049_);
v___x_2051_ = v___x_2046_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_1210__overap_2052_; lean_object* v___x_2053_; 
v___x_1210__overap_2052_ = l_liftExcept___redArg(v___x_2010_, v___x_2011_, v___x_2051_);
lean_inc_ref(v___y_2013_);
v___x_2053_ = lean_apply_2(v___x_1210__overap_2052_, v___y_2013_, v_a_2043_);
return v___x_2053_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v___x_2011_);
lean_dec_ref(v___x_2010_);
v_a_2058_ = lean_ctor_get(v___x_2015_, 0);
v_a_2059_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2015_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_inc(v_a_2058_);
lean_dec(v___x_2015_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2058_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2067_, lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v_stx_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2067_, v___x_2068_, v___x_2069_, v_stx_2070_, v___y_2071_, v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2074_, lean_object* v_declName_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
uint8_t v___x_2078_; lean_object* v_env_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; uint8_t v___x_2082_; 
v___x_2078_ = 0;
v_env_2079_ = l_Lean_Environment_setExporting(v_env_2074_, v___x_2078_);
lean_inc(v_declName_2075_);
v___x_2080_ = l_Lean_mkPrivateName(v_env_2079_, v_declName_2075_);
v___x_2081_ = 1;
lean_inc_ref(v_env_2079_);
v___x_2082_ = l_Lean_Environment_contains(v_env_2079_, v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2083_ = l_Lean_privateToUserName(v_declName_2075_);
v___x_2084_ = l_Lean_Environment_contains(v_env_2079_, v___x_2083_, v___x_2081_);
v___x_2085_ = lean_box(v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___y_2077_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v_env_2079_);
lean_dec(v_declName_2075_);
v___x_2087_ = lean_box(v___x_2082_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___y_2077_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2089_, lean_object* v_declName_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2089_, v_declName_2090_, v___y_2091_, v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2094_, lean_object* v_currNamespace_2095_, lean_object* v_openDecls_2096_, lean_object* v_n_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = l_Lean_ResolveName_resolveNamespace(v_env_2094_, v_currNamespace_2095_, v_openDecls_2096_, v_n_2097_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2102_, lean_object* v_currNamespace_2103_, lean_object* v_openDecls_2104_, lean_object* v_n_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2102_, v_currNamespace_2103_, v_openDecls_2104_, v_n_2105_, v___y_2106_, v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2109_, lean_object* v_opts_2110_, lean_object* v_currNamespace_2111_, lean_object* v_openDecls_2112_, lean_object* v_n_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = l_Lean_ResolveName_resolveGlobalName(v_env_2109_, v_opts_2110_, v_currNamespace_2111_, v_openDecls_2112_, v_n_2113_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2118_, lean_object* v_opts_2119_, lean_object* v_currNamespace_2120_, lean_object* v_openDecls_2121_, lean_object* v_n_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2118_, v_opts_2119_, v_currNamespace_2120_, v_openDecls_2121_, v_n_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec_ref(v_opts_2119_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2126_, lean_object* v_a_2127_, lean_object* v_____r_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_apply_2(v_toPure_2126_, lean_box(0), v_a_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2130_, lean_object* v_inst_2131_, lean_object* v___f_2132_, lean_object* v_toBind_2133_, lean_object* v___f_2134_, lean_object* v_____r_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = l_List_reverse___redArg(v_traceMsgs_2130_);
v___x_2137_ = l_List_forM___redArg(v_inst_2131_, v___x_2136_, v___f_2132_);
v___x_2138_ = lean_apply_4(v_toBind_2133_, lean_box(0), lean_box(0), v___x_2137_, v___f_2134_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2139_, lean_object* v_macroScope_2140_, lean_object* v_toBind_2141_, lean_object* v___f_2142_, lean_object* v_____s_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_apply_1(v_setNextMacroScope_2139_, v_macroScope_2140_);
v___x_2145_ = lean_apply_4(v_toBind_2141_, lean_box(0), lean_box(0), v___x_2144_, v___f_2142_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2146_, lean_object* v_toPure_2147_, lean_object* v_____r_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2146_);
v___x_2150_ = lean_apply_2(v_toPure_2147_, lean_box(0), v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_toMonadRef_2155_, lean_object* v_inst_2156_, lean_object* v_toBind_2157_, lean_object* v___f_2158_, lean_object* v_a_2159_, lean_object* v_x_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = 1;
v___x_2163_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2151_, v_inst_2152_, v_inst_2153_, v_inst_2154_, v_toMonadRef_2155_, v_inst_2156_, v_a_2159_, v___x_2162_);
v___x_2164_ = lean_apply_4(v_toBind_2157_, lean_box(0), lean_box(0), v___x_2163_, v___f_2158_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2166_, lean_object* v_____do__lift_2167_, lean_object* v_____do__lift_2168_, lean_object* v_____do__lift_2169_, lean_object* v_____do__lift_2170_, lean_object* v_____do__lift_2171_, lean_object* v_x_2172_, lean_object* v_toPure_2173_, lean_object* v_inst_2174_, lean_object* v___f_2175_, lean_object* v_toBind_2176_, lean_object* v_setNextMacroScope_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_toMonadRef_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_, lean_object* v_toMonadExceptOf_2184_, lean_object* v_____do__lift_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2186_, 0, v_methods_2166_);
lean_ctor_set(v___x_2186_, 1, v_____do__lift_2167_);
lean_ctor_set(v___x_2186_, 2, v_____do__lift_2168_);
lean_ctor_set(v___x_2186_, 3, v_____do__lift_2169_);
lean_ctor_set(v___x_2186_, 4, v_____do__lift_2170_);
lean_ctor_set(v___x_2186_, 5, v_____do__lift_2171_);
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2188_, 0, v_____do__lift_2185_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
v___x_2189_ = lean_apply_2(v_x_2172_, v___x_2186_, v___x_2188_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_a_2191_; lean_object* v_macroScope_2192_; lean_object* v_traceMsgs_2193_; lean_object* v_expandedMacroDecls_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_toMonadExceptOf_2184_);
lean_dec_ref(v_inst_2183_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_a_2190_);
v_a_2191_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2189_, 2);
v_macroScope_2192_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_macroScope_2192_);
v_traceMsgs_2193_ = lean_ctor_get(v_a_2190_, 1);
lean_inc(v_traceMsgs_2193_);
v_expandedMacroDecls_2194_ = lean_ctor_get(v_a_2190_, 2);
lean_inc(v_expandedMacroDecls_2194_);
lean_dec(v_a_2190_);
lean_inc(v_toPure_2173_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2195_, 0, v_toPure_2173_);
lean_closure_set(v___f_2195_, 1, v_a_2191_);
lean_inc_n(v_toBind_2176_, 3);
lean_inc_ref_n(v_inst_2174_, 2);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2196_, 0, v_traceMsgs_2193_);
lean_closure_set(v___f_2196_, 1, v_inst_2174_);
lean_closure_set(v___f_2196_, 2, v___f_2175_);
lean_closure_set(v___f_2196_, 3, v_toBind_2176_);
lean_closure_set(v___f_2196_, 4, v___f_2195_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2197_, 0, v_setNextMacroScope_2177_);
lean_closure_set(v___f_2197_, 1, v_macroScope_2192_);
lean_closure_set(v___f_2197_, 2, v_toBind_2176_);
lean_closure_set(v___f_2197_, 3, v___f_2196_);
v___x_2198_ = lean_box(0);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2199_, 0, v___x_2198_);
lean_closure_set(v___f_2199_, 1, v_toPure_2173_);
v___f_2200_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2200_, 0, v_inst_2174_);
lean_closure_set(v___f_2200_, 1, v_inst_2178_);
lean_closure_set(v___f_2200_, 2, v_inst_2179_);
lean_closure_set(v___f_2200_, 3, v_inst_2180_);
lean_closure_set(v___f_2200_, 4, v_toMonadRef_2181_);
lean_closure_set(v___f_2200_, 5, v_inst_2182_);
lean_closure_set(v___f_2200_, 6, v_toBind_2176_);
lean_closure_set(v___f_2200_, 7, v___f_2199_);
v___x_2201_ = l_List_forIn_x27_loop___redArg(v_inst_2174_, v___f_2200_, v_expandedMacroDecls_2194_, v___x_2198_);
lean_dec(v_expandedMacroDecls_2194_);
v___x_2202_ = lean_apply_4(v_toBind_2176_, lean_box(0), lean_box(0), v___x_2201_, v___f_2197_);
return v___x_2202_;
}
else
{
lean_object* v_a_2203_; 
lean_dec(v_inst_2182_);
lean_dec_ref(v_toMonadRef_2181_);
lean_dec_ref(v_inst_2180_);
lean_dec_ref(v_inst_2179_);
lean_dec_ref(v_inst_2178_);
lean_dec(v_setNextMacroScope_2177_);
lean_dec(v_toBind_2176_);
lean_dec(v___f_2175_);
lean_dec(v_toPure_2173_);
v_a_2203_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2189_, 2);
if (lean_obj_tag(v_a_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_a_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
lean_dec_ref(v_toMonadExceptOf_2184_);
v_a_2204_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_a_2204_);
v_a_2205_ = lean_ctor_get(v_a_2203_, 1);
lean_inc_ref(v_a_2205_);
lean_dec_ref_known(v_a_2203_, 2);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2207_ = lean_string_dec_eq(v_a_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2205_);
v___x_2209_ = l_Lean_MessageData_ofFormat(v___x_2208_);
v___x_2210_ = l_Lean_throwErrorAt___redArg(v_inst_2174_, v_inst_2183_, v_a_2204_, v___x_2209_);
return v___x_2210_;
}
else
{
lean_object* v___x_2211_; 
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_inst_2174_);
v___x_2211_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2183_, v_a_2204_);
return v___x_2211_;
}
}
else
{
lean_object* v___x_2212_; 
lean_dec_ref(v_inst_2183_);
lean_dec_ref(v_inst_2174_);
v___x_2212_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2184_);
return v___x_2212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2213_ = _args[0];
lean_object* v_____do__lift_2214_ = _args[1];
lean_object* v_____do__lift_2215_ = _args[2];
lean_object* v_____do__lift_2216_ = _args[3];
lean_object* v_____do__lift_2217_ = _args[4];
lean_object* v_____do__lift_2218_ = _args[5];
lean_object* v_x_2219_ = _args[6];
lean_object* v_toPure_2220_ = _args[7];
lean_object* v_inst_2221_ = _args[8];
lean_object* v___f_2222_ = _args[9];
lean_object* v_toBind_2223_ = _args[10];
lean_object* v_setNextMacroScope_2224_ = _args[11];
lean_object* v_inst_2225_ = _args[12];
lean_object* v_inst_2226_ = _args[13];
lean_object* v_inst_2227_ = _args[14];
lean_object* v_toMonadRef_2228_ = _args[15];
lean_object* v_inst_2229_ = _args[16];
lean_object* v_inst_2230_ = _args[17];
lean_object* v_toMonadExceptOf_2231_ = _args[18];
lean_object* v_____do__lift_2232_ = _args[19];
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2213_, v_____do__lift_2214_, v_____do__lift_2215_, v_____do__lift_2216_, v_____do__lift_2217_, v_____do__lift_2218_, v_x_2219_, v_toPure_2220_, v_inst_2221_, v___f_2222_, v_toBind_2223_, v_setNextMacroScope_2224_, v_inst_2225_, v_inst_2226_, v_inst_2227_, v_toMonadRef_2228_, v_inst_2229_, v_inst_2230_, v_toMonadExceptOf_2231_, v_____do__lift_2232_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2234_, lean_object* v_____do__lift_2235_, lean_object* v_____do__lift_2236_, lean_object* v_____do__lift_2237_, lean_object* v_____do__lift_2238_, lean_object* v_x_2239_, lean_object* v_toPure_2240_, lean_object* v_inst_2241_, lean_object* v___f_2242_, lean_object* v_toBind_2243_, lean_object* v_setNextMacroScope_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_toMonadRef_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_toMonadExceptOf_2251_, lean_object* v_getNextMacroScope_2252_, lean_object* v_____do__lift_2253_){
_start:
{
lean_object* v___f_2254_; lean_object* v___x_2255_; 
lean_inc(v_toBind_2243_);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2254_, 0, v_methods_2234_);
lean_closure_set(v___f_2254_, 1, v_____do__lift_2235_);
lean_closure_set(v___f_2254_, 2, v_____do__lift_2236_);
lean_closure_set(v___f_2254_, 3, v_____do__lift_2237_);
lean_closure_set(v___f_2254_, 4, v_____do__lift_2253_);
lean_closure_set(v___f_2254_, 5, v_____do__lift_2238_);
lean_closure_set(v___f_2254_, 6, v_x_2239_);
lean_closure_set(v___f_2254_, 7, v_toPure_2240_);
lean_closure_set(v___f_2254_, 8, v_inst_2241_);
lean_closure_set(v___f_2254_, 9, v___f_2242_);
lean_closure_set(v___f_2254_, 10, v_toBind_2243_);
lean_closure_set(v___f_2254_, 11, v_setNextMacroScope_2244_);
lean_closure_set(v___f_2254_, 12, v_inst_2245_);
lean_closure_set(v___f_2254_, 13, v_inst_2246_);
lean_closure_set(v___f_2254_, 14, v_inst_2247_);
lean_closure_set(v___f_2254_, 15, v_toMonadRef_2248_);
lean_closure_set(v___f_2254_, 16, v_inst_2249_);
lean_closure_set(v___f_2254_, 17, v_inst_2250_);
lean_closure_set(v___f_2254_, 18, v_toMonadExceptOf_2251_);
v___x_2255_ = lean_apply_4(v_toBind_2243_, lean_box(0), lean_box(0), v_getNextMacroScope_2252_, v___f_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2256_ = _args[0];
lean_object* v_____do__lift_2257_ = _args[1];
lean_object* v_____do__lift_2258_ = _args[2];
lean_object* v_____do__lift_2259_ = _args[3];
lean_object* v_____do__lift_2260_ = _args[4];
lean_object* v_x_2261_ = _args[5];
lean_object* v_toPure_2262_ = _args[6];
lean_object* v_inst_2263_ = _args[7];
lean_object* v___f_2264_ = _args[8];
lean_object* v_toBind_2265_ = _args[9];
lean_object* v_setNextMacroScope_2266_ = _args[10];
lean_object* v_inst_2267_ = _args[11];
lean_object* v_inst_2268_ = _args[12];
lean_object* v_inst_2269_ = _args[13];
lean_object* v_toMonadRef_2270_ = _args[14];
lean_object* v_inst_2271_ = _args[15];
lean_object* v_inst_2272_ = _args[16];
lean_object* v_toMonadExceptOf_2273_ = _args[17];
lean_object* v_getNextMacroScope_2274_ = _args[18];
lean_object* v_____do__lift_2275_ = _args[19];
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2256_, v_____do__lift_2257_, v_____do__lift_2258_, v_____do__lift_2259_, v_____do__lift_2260_, v_x_2261_, v_toPure_2262_, v_inst_2263_, v___f_2264_, v_toBind_2265_, v_setNextMacroScope_2266_, v_inst_2267_, v_inst_2268_, v_inst_2269_, v_toMonadRef_2270_, v_inst_2271_, v_inst_2272_, v_toMonadExceptOf_2273_, v_getNextMacroScope_2274_, v_____do__lift_2275_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2277_, lean_object* v_____do__lift_2278_, lean_object* v_____do__lift_2279_, lean_object* v_____do__lift_2280_, lean_object* v_x_2281_, lean_object* v_toPure_2282_, lean_object* v_inst_2283_, lean_object* v___f_2284_, lean_object* v_toBind_2285_, lean_object* v_setNextMacroScope_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_toMonadRef_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_toMonadExceptOf_2293_, lean_object* v_getNextMacroScope_2294_, lean_object* v_getMaxRecDepth_2295_, lean_object* v_____do__lift_2296_){
_start:
{
lean_object* v___f_2297_; lean_object* v___x_2298_; 
lean_inc(v_toBind_2285_);
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2297_, 0, v_methods_2277_);
lean_closure_set(v___f_2297_, 1, v_____do__lift_2278_);
lean_closure_set(v___f_2297_, 2, v_____do__lift_2279_);
lean_closure_set(v___f_2297_, 3, v_____do__lift_2296_);
lean_closure_set(v___f_2297_, 4, v_____do__lift_2280_);
lean_closure_set(v___f_2297_, 5, v_x_2281_);
lean_closure_set(v___f_2297_, 6, v_toPure_2282_);
lean_closure_set(v___f_2297_, 7, v_inst_2283_);
lean_closure_set(v___f_2297_, 8, v___f_2284_);
lean_closure_set(v___f_2297_, 9, v_toBind_2285_);
lean_closure_set(v___f_2297_, 10, v_setNextMacroScope_2286_);
lean_closure_set(v___f_2297_, 11, v_inst_2287_);
lean_closure_set(v___f_2297_, 12, v_inst_2288_);
lean_closure_set(v___f_2297_, 13, v_inst_2289_);
lean_closure_set(v___f_2297_, 14, v_toMonadRef_2290_);
lean_closure_set(v___f_2297_, 15, v_inst_2291_);
lean_closure_set(v___f_2297_, 16, v_inst_2292_);
lean_closure_set(v___f_2297_, 17, v_toMonadExceptOf_2293_);
lean_closure_set(v___f_2297_, 18, v_getNextMacroScope_2294_);
v___x_2298_ = lean_apply_4(v_toBind_2285_, lean_box(0), lean_box(0), v_getMaxRecDepth_2295_, v___f_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2299_ = _args[0];
lean_object* v_____do__lift_2300_ = _args[1];
lean_object* v_____do__lift_2301_ = _args[2];
lean_object* v_____do__lift_2302_ = _args[3];
lean_object* v_x_2303_ = _args[4];
lean_object* v_toPure_2304_ = _args[5];
lean_object* v_inst_2305_ = _args[6];
lean_object* v___f_2306_ = _args[7];
lean_object* v_toBind_2307_ = _args[8];
lean_object* v_setNextMacroScope_2308_ = _args[9];
lean_object* v_inst_2309_ = _args[10];
lean_object* v_inst_2310_ = _args[11];
lean_object* v_inst_2311_ = _args[12];
lean_object* v_toMonadRef_2312_ = _args[13];
lean_object* v_inst_2313_ = _args[14];
lean_object* v_inst_2314_ = _args[15];
lean_object* v_toMonadExceptOf_2315_ = _args[16];
lean_object* v_getNextMacroScope_2316_ = _args[17];
lean_object* v_getMaxRecDepth_2317_ = _args[18];
lean_object* v_____do__lift_2318_ = _args[19];
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2299_, v_____do__lift_2300_, v_____do__lift_2301_, v_____do__lift_2302_, v_x_2303_, v_toPure_2304_, v_inst_2305_, v___f_2306_, v_toBind_2307_, v_setNextMacroScope_2308_, v_inst_2309_, v_inst_2310_, v_inst_2311_, v_toMonadRef_2312_, v_inst_2313_, v_inst_2314_, v_toMonadExceptOf_2315_, v_getNextMacroScope_2316_, v_getMaxRecDepth_2317_, v_____do__lift_2318_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2320_, lean_object* v_methods_2321_, lean_object* v_____do__lift_2322_, lean_object* v_____do__lift_2323_, lean_object* v_x_2324_, lean_object* v_toPure_2325_, lean_object* v_inst_2326_, lean_object* v___f_2327_, lean_object* v_toBind_2328_, lean_object* v_setNextMacroScope_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_toMonadRef_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_toMonadExceptOf_2336_, lean_object* v_getNextMacroScope_2337_, lean_object* v_____do__lift_2338_){
_start:
{
lean_object* v_getRecDepth_2339_; lean_object* v_getMaxRecDepth_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; 
v_getRecDepth_2339_ = lean_ctor_get(v_inst_2320_, 1);
lean_inc(v_getRecDepth_2339_);
v_getMaxRecDepth_2340_ = lean_ctor_get(v_inst_2320_, 2);
lean_inc(v_getMaxRecDepth_2340_);
lean_dec_ref(v_inst_2320_);
lean_inc(v_toBind_2328_);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2341_, 0, v_methods_2321_);
lean_closure_set(v___f_2341_, 1, v_____do__lift_2338_);
lean_closure_set(v___f_2341_, 2, v_____do__lift_2322_);
lean_closure_set(v___f_2341_, 3, v_____do__lift_2323_);
lean_closure_set(v___f_2341_, 4, v_x_2324_);
lean_closure_set(v___f_2341_, 5, v_toPure_2325_);
lean_closure_set(v___f_2341_, 6, v_inst_2326_);
lean_closure_set(v___f_2341_, 7, v___f_2327_);
lean_closure_set(v___f_2341_, 8, v_toBind_2328_);
lean_closure_set(v___f_2341_, 9, v_setNextMacroScope_2329_);
lean_closure_set(v___f_2341_, 10, v_inst_2330_);
lean_closure_set(v___f_2341_, 11, v_inst_2331_);
lean_closure_set(v___f_2341_, 12, v_inst_2332_);
lean_closure_set(v___f_2341_, 13, v_toMonadRef_2333_);
lean_closure_set(v___f_2341_, 14, v_inst_2334_);
lean_closure_set(v___f_2341_, 15, v_inst_2335_);
lean_closure_set(v___f_2341_, 16, v_toMonadExceptOf_2336_);
lean_closure_set(v___f_2341_, 17, v_getNextMacroScope_2337_);
lean_closure_set(v___f_2341_, 18, v_getMaxRecDepth_2340_);
v___x_2342_ = lean_apply_4(v_toBind_2328_, lean_box(0), lean_box(0), v_getRecDepth_2339_, v___f_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2343_ = _args[0];
lean_object* v_methods_2344_ = _args[1];
lean_object* v_____do__lift_2345_ = _args[2];
lean_object* v_____do__lift_2346_ = _args[3];
lean_object* v_x_2347_ = _args[4];
lean_object* v_toPure_2348_ = _args[5];
lean_object* v_inst_2349_ = _args[6];
lean_object* v___f_2350_ = _args[7];
lean_object* v_toBind_2351_ = _args[8];
lean_object* v_setNextMacroScope_2352_ = _args[9];
lean_object* v_inst_2353_ = _args[10];
lean_object* v_inst_2354_ = _args[11];
lean_object* v_inst_2355_ = _args[12];
lean_object* v_toMonadRef_2356_ = _args[13];
lean_object* v_inst_2357_ = _args[14];
lean_object* v_inst_2358_ = _args[15];
lean_object* v_toMonadExceptOf_2359_ = _args[16];
lean_object* v_getNextMacroScope_2360_ = _args[17];
lean_object* v_____do__lift_2361_ = _args[18];
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2343_, v_methods_2344_, v_____do__lift_2345_, v_____do__lift_2346_, v_x_2347_, v_toPure_2348_, v_inst_2349_, v___f_2350_, v_toBind_2351_, v_setNextMacroScope_2352_, v_inst_2353_, v_inst_2354_, v_inst_2355_, v_toMonadRef_2356_, v_inst_2357_, v_inst_2358_, v_toMonadExceptOf_2359_, v_getNextMacroScope_2360_, v_____do__lift_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2363_, lean_object* v_methods_2364_, lean_object* v_____do__lift_2365_, lean_object* v_x_2366_, lean_object* v_toPure_2367_, lean_object* v_inst_2368_, lean_object* v___f_2369_, lean_object* v_toBind_2370_, lean_object* v_setNextMacroScope_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_toMonadRef_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_toMonadExceptOf_2378_, lean_object* v_getNextMacroScope_2379_, lean_object* v_getContext_2380_, lean_object* v_____do__lift_2381_){
_start:
{
lean_object* v___f_2382_; lean_object* v___x_2383_; 
lean_inc(v_toBind_2370_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2382_, 0, v_inst_2363_);
lean_closure_set(v___f_2382_, 1, v_methods_2364_);
lean_closure_set(v___f_2382_, 2, v_____do__lift_2381_);
lean_closure_set(v___f_2382_, 3, v_____do__lift_2365_);
lean_closure_set(v___f_2382_, 4, v_x_2366_);
lean_closure_set(v___f_2382_, 5, v_toPure_2367_);
lean_closure_set(v___f_2382_, 6, v_inst_2368_);
lean_closure_set(v___f_2382_, 7, v___f_2369_);
lean_closure_set(v___f_2382_, 8, v_toBind_2370_);
lean_closure_set(v___f_2382_, 9, v_setNextMacroScope_2371_);
lean_closure_set(v___f_2382_, 10, v_inst_2372_);
lean_closure_set(v___f_2382_, 11, v_inst_2373_);
lean_closure_set(v___f_2382_, 12, v_inst_2374_);
lean_closure_set(v___f_2382_, 13, v_toMonadRef_2375_);
lean_closure_set(v___f_2382_, 14, v_inst_2376_);
lean_closure_set(v___f_2382_, 15, v_inst_2377_);
lean_closure_set(v___f_2382_, 16, v_toMonadExceptOf_2378_);
lean_closure_set(v___f_2382_, 17, v_getNextMacroScope_2379_);
v___x_2383_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v_getContext_2380_, v___f_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2384_ = _args[0];
lean_object* v_methods_2385_ = _args[1];
lean_object* v_____do__lift_2386_ = _args[2];
lean_object* v_x_2387_ = _args[3];
lean_object* v_toPure_2388_ = _args[4];
lean_object* v_inst_2389_ = _args[5];
lean_object* v___f_2390_ = _args[6];
lean_object* v_toBind_2391_ = _args[7];
lean_object* v_setNextMacroScope_2392_ = _args[8];
lean_object* v_inst_2393_ = _args[9];
lean_object* v_inst_2394_ = _args[10];
lean_object* v_inst_2395_ = _args[11];
lean_object* v_toMonadRef_2396_ = _args[12];
lean_object* v_inst_2397_ = _args[13];
lean_object* v_inst_2398_ = _args[14];
lean_object* v_toMonadExceptOf_2399_ = _args[15];
lean_object* v_getNextMacroScope_2400_ = _args[16];
lean_object* v_getContext_2401_ = _args[17];
lean_object* v_____do__lift_2402_ = _args[18];
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2384_, v_methods_2385_, v_____do__lift_2386_, v_x_2387_, v_toPure_2388_, v_inst_2389_, v___f_2390_, v_toBind_2391_, v_setNextMacroScope_2392_, v_inst_2393_, v_inst_2394_, v_inst_2395_, v_toMonadRef_2396_, v_inst_2397_, v_inst_2398_, v_toMonadExceptOf_2399_, v_getNextMacroScope_2400_, v_getContext_2401_, v_____do__lift_2402_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2404_, lean_object* v_inst_2405_, lean_object* v_methods_2406_, lean_object* v_x_2407_, lean_object* v_toPure_2408_, lean_object* v_inst_2409_, lean_object* v___f_2410_, lean_object* v_toBind_2411_, lean_object* v_setNextMacroScope_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_toMonadRef_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_toMonadExceptOf_2419_, lean_object* v_getNextMacroScope_2420_, lean_object* v_____do__lift_2421_){
_start:
{
lean_object* v_getCurrMacroScope_2422_; lean_object* v_getContext_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; 
v_getCurrMacroScope_2422_ = lean_ctor_get(v_toMonadQuotation_2404_, 1);
lean_inc(v_getCurrMacroScope_2422_);
v_getContext_2423_ = lean_ctor_get(v_toMonadQuotation_2404_, 2);
lean_inc(v_getContext_2423_);
lean_dec_ref(v_toMonadQuotation_2404_);
lean_inc(v_toBind_2411_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2424_, 0, v_inst_2405_);
lean_closure_set(v___f_2424_, 1, v_methods_2406_);
lean_closure_set(v___f_2424_, 2, v_____do__lift_2421_);
lean_closure_set(v___f_2424_, 3, v_x_2407_);
lean_closure_set(v___f_2424_, 4, v_toPure_2408_);
lean_closure_set(v___f_2424_, 5, v_inst_2409_);
lean_closure_set(v___f_2424_, 6, v___f_2410_);
lean_closure_set(v___f_2424_, 7, v_toBind_2411_);
lean_closure_set(v___f_2424_, 8, v_setNextMacroScope_2412_);
lean_closure_set(v___f_2424_, 9, v_inst_2413_);
lean_closure_set(v___f_2424_, 10, v_inst_2414_);
lean_closure_set(v___f_2424_, 11, v_inst_2415_);
lean_closure_set(v___f_2424_, 12, v_toMonadRef_2416_);
lean_closure_set(v___f_2424_, 13, v_inst_2417_);
lean_closure_set(v___f_2424_, 14, v_inst_2418_);
lean_closure_set(v___f_2424_, 15, v_toMonadExceptOf_2419_);
lean_closure_set(v___f_2424_, 16, v_getNextMacroScope_2420_);
lean_closure_set(v___f_2424_, 17, v_getContext_2423_);
v___x_2425_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v_getCurrMacroScope_2422_, v___f_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2426_ = _args[0];
lean_object* v_inst_2427_ = _args[1];
lean_object* v_methods_2428_ = _args[2];
lean_object* v_x_2429_ = _args[3];
lean_object* v_toPure_2430_ = _args[4];
lean_object* v_inst_2431_ = _args[5];
lean_object* v___f_2432_ = _args[6];
lean_object* v_toBind_2433_ = _args[7];
lean_object* v_setNextMacroScope_2434_ = _args[8];
lean_object* v_inst_2435_ = _args[9];
lean_object* v_inst_2436_ = _args[10];
lean_object* v_inst_2437_ = _args[11];
lean_object* v_toMonadRef_2438_ = _args[12];
lean_object* v_inst_2439_ = _args[13];
lean_object* v_inst_2440_ = _args[14];
lean_object* v_toMonadExceptOf_2441_ = _args[15];
lean_object* v_getNextMacroScope_2442_ = _args[16];
lean_object* v_____do__lift_2443_ = _args[17];
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2426_, v_inst_2427_, v_methods_2428_, v_x_2429_, v_toPure_2430_, v_inst_2431_, v___f_2432_, v_toBind_2433_, v_setNextMacroScope_2434_, v_inst_2435_, v_inst_2436_, v_inst_2437_, v_toMonadRef_2438_, v_inst_2439_, v_inst_2440_, v_toMonadExceptOf_2441_, v_getNextMacroScope_2442_, v_____do__lift_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2445_, lean_object* v_env_2446_, lean_object* v_currNamespace_2447_, lean_object* v_opts_2448_, lean_object* v___x_2449_, lean_object* v___f_2450_, lean_object* v___f_2451_, lean_object* v_toMonadQuotation_2452_, lean_object* v_inst_2453_, lean_object* v_x_2454_, lean_object* v_toPure_2455_, lean_object* v_inst_2456_, lean_object* v___f_2457_, lean_object* v_toBind_2458_, lean_object* v_setNextMacroScope_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_toMonadExceptOf_2465_, lean_object* v_getNextMacroScope_2466_, lean_object* v_openDecls_2467_){
_start:
{
lean_object* v_getRef_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; lean_object* v_methods_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; 
v_getRef_2468_ = lean_ctor_get(v_toMonadRef_2445_, 0);
lean_inc(v_getRef_2468_);
lean_inc(v_openDecls_2467_);
lean_inc_n(v_currNamespace_2447_, 2);
lean_inc_ref(v_env_2446_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2469_, 0, v_env_2446_);
lean_closure_set(v___f_2469_, 1, v_currNamespace_2447_);
lean_closure_set(v___f_2469_, 2, v_openDecls_2467_);
v___f_2470_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2470_, 0, v_env_2446_);
lean_closure_set(v___f_2470_, 1, v_opts_2448_);
lean_closure_set(v___f_2470_, 2, v_currNamespace_2447_);
lean_closure_set(v___f_2470_, 3, v_openDecls_2467_);
v___x_2471_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2471_, 0, lean_box(0));
lean_closure_set(v___x_2471_, 1, lean_box(0));
lean_closure_set(v___x_2471_, 2, v___x_2449_);
lean_closure_set(v___x_2471_, 3, lean_box(0));
lean_closure_set(v___x_2471_, 4, v_currNamespace_2447_);
v_methods_2472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2472_, 0, v___f_2450_);
lean_ctor_set(v_methods_2472_, 1, v___x_2471_);
lean_ctor_set(v_methods_2472_, 2, v___f_2451_);
lean_ctor_set(v_methods_2472_, 3, v___f_2469_);
lean_ctor_set(v_methods_2472_, 4, v___f_2470_);
lean_inc(v_toBind_2458_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2473_, 0, v_toMonadQuotation_2452_);
lean_closure_set(v___f_2473_, 1, v_inst_2453_);
lean_closure_set(v___f_2473_, 2, v_methods_2472_);
lean_closure_set(v___f_2473_, 3, v_x_2454_);
lean_closure_set(v___f_2473_, 4, v_toPure_2455_);
lean_closure_set(v___f_2473_, 5, v_inst_2456_);
lean_closure_set(v___f_2473_, 6, v___f_2457_);
lean_closure_set(v___f_2473_, 7, v_toBind_2458_);
lean_closure_set(v___f_2473_, 8, v_setNextMacroScope_2459_);
lean_closure_set(v___f_2473_, 9, v_inst_2460_);
lean_closure_set(v___f_2473_, 10, v_inst_2461_);
lean_closure_set(v___f_2473_, 11, v_inst_2462_);
lean_closure_set(v___f_2473_, 12, v_toMonadRef_2445_);
lean_closure_set(v___f_2473_, 13, v_inst_2463_);
lean_closure_set(v___f_2473_, 14, v_inst_2464_);
lean_closure_set(v___f_2473_, 15, v_toMonadExceptOf_2465_);
lean_closure_set(v___f_2473_, 16, v_getNextMacroScope_2466_);
v___x_2474_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v_getRef_2468_, v___f_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2475_ = _args[0];
lean_object* v_env_2476_ = _args[1];
lean_object* v_currNamespace_2477_ = _args[2];
lean_object* v_opts_2478_ = _args[3];
lean_object* v___x_2479_ = _args[4];
lean_object* v___f_2480_ = _args[5];
lean_object* v___f_2481_ = _args[6];
lean_object* v_toMonadQuotation_2482_ = _args[7];
lean_object* v_inst_2483_ = _args[8];
lean_object* v_x_2484_ = _args[9];
lean_object* v_toPure_2485_ = _args[10];
lean_object* v_inst_2486_ = _args[11];
lean_object* v___f_2487_ = _args[12];
lean_object* v_toBind_2488_ = _args[13];
lean_object* v_setNextMacroScope_2489_ = _args[14];
lean_object* v_inst_2490_ = _args[15];
lean_object* v_inst_2491_ = _args[16];
lean_object* v_inst_2492_ = _args[17];
lean_object* v_inst_2493_ = _args[18];
lean_object* v_inst_2494_ = _args[19];
lean_object* v_toMonadExceptOf_2495_ = _args[20];
lean_object* v_getNextMacroScope_2496_ = _args[21];
lean_object* v_openDecls_2497_ = _args[22];
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2475_, v_env_2476_, v_currNamespace_2477_, v_opts_2478_, v___x_2479_, v___f_2480_, v___f_2481_, v_toMonadQuotation_2482_, v_inst_2483_, v_x_2484_, v_toPure_2485_, v_inst_2486_, v___f_2487_, v_toBind_2488_, v_setNextMacroScope_2489_, v_inst_2490_, v_inst_2491_, v_inst_2492_, v_inst_2493_, v_inst_2494_, v_toMonadExceptOf_2495_, v_getNextMacroScope_2496_, v_openDecls_2497_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2499_, lean_object* v_env_2500_, lean_object* v_opts_2501_, lean_object* v___x_2502_, lean_object* v___f_2503_, lean_object* v___f_2504_, lean_object* v_toMonadQuotation_2505_, lean_object* v_inst_2506_, lean_object* v_x_2507_, lean_object* v_toPure_2508_, lean_object* v_inst_2509_, lean_object* v___f_2510_, lean_object* v_toBind_2511_, lean_object* v_setNextMacroScope_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_toMonadExceptOf_2518_, lean_object* v_getNextMacroScope_2519_, lean_object* v_getOpenDecls_2520_, lean_object* v_currNamespace_2521_){
_start:
{
lean_object* v___f_2522_; lean_object* v___x_2523_; 
lean_inc(v_toBind_2511_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2522_, 0, v_toMonadRef_2499_);
lean_closure_set(v___f_2522_, 1, v_env_2500_);
lean_closure_set(v___f_2522_, 2, v_currNamespace_2521_);
lean_closure_set(v___f_2522_, 3, v_opts_2501_);
lean_closure_set(v___f_2522_, 4, v___x_2502_);
lean_closure_set(v___f_2522_, 5, v___f_2503_);
lean_closure_set(v___f_2522_, 6, v___f_2504_);
lean_closure_set(v___f_2522_, 7, v_toMonadQuotation_2505_);
lean_closure_set(v___f_2522_, 8, v_inst_2506_);
lean_closure_set(v___f_2522_, 9, v_x_2507_);
lean_closure_set(v___f_2522_, 10, v_toPure_2508_);
lean_closure_set(v___f_2522_, 11, v_inst_2509_);
lean_closure_set(v___f_2522_, 12, v___f_2510_);
lean_closure_set(v___f_2522_, 13, v_toBind_2511_);
lean_closure_set(v___f_2522_, 14, v_setNextMacroScope_2512_);
lean_closure_set(v___f_2522_, 15, v_inst_2513_);
lean_closure_set(v___f_2522_, 16, v_inst_2514_);
lean_closure_set(v___f_2522_, 17, v_inst_2515_);
lean_closure_set(v___f_2522_, 18, v_inst_2516_);
lean_closure_set(v___f_2522_, 19, v_inst_2517_);
lean_closure_set(v___f_2522_, 20, v_toMonadExceptOf_2518_);
lean_closure_set(v___f_2522_, 21, v_getNextMacroScope_2519_);
v___x_2523_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v_getOpenDecls_2520_, v___f_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2524_ = _args[0];
lean_object* v_env_2525_ = _args[1];
lean_object* v_opts_2526_ = _args[2];
lean_object* v___x_2527_ = _args[3];
lean_object* v___f_2528_ = _args[4];
lean_object* v___f_2529_ = _args[5];
lean_object* v_toMonadQuotation_2530_ = _args[6];
lean_object* v_inst_2531_ = _args[7];
lean_object* v_x_2532_ = _args[8];
lean_object* v_toPure_2533_ = _args[9];
lean_object* v_inst_2534_ = _args[10];
lean_object* v___f_2535_ = _args[11];
lean_object* v_toBind_2536_ = _args[12];
lean_object* v_setNextMacroScope_2537_ = _args[13];
lean_object* v_inst_2538_ = _args[14];
lean_object* v_inst_2539_ = _args[15];
lean_object* v_inst_2540_ = _args[16];
lean_object* v_inst_2541_ = _args[17];
lean_object* v_inst_2542_ = _args[18];
lean_object* v_toMonadExceptOf_2543_ = _args[19];
lean_object* v_getNextMacroScope_2544_ = _args[20];
lean_object* v_getOpenDecls_2545_ = _args[21];
lean_object* v_currNamespace_2546_ = _args[22];
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2524_, v_env_2525_, v_opts_2526_, v___x_2527_, v___f_2528_, v___f_2529_, v_toMonadQuotation_2530_, v_inst_2531_, v_x_2532_, v_toPure_2533_, v_inst_2534_, v___f_2535_, v_toBind_2536_, v_setNextMacroScope_2537_, v_inst_2538_, v_inst_2539_, v_inst_2540_, v_inst_2541_, v_inst_2542_, v_toMonadExceptOf_2543_, v_getNextMacroScope_2544_, v_getOpenDecls_2545_, v_currNamespace_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2548_, lean_object* v_toMonadRef_2549_, lean_object* v_env_2550_, lean_object* v___x_2551_, lean_object* v___f_2552_, lean_object* v___f_2553_, lean_object* v_toMonadQuotation_2554_, lean_object* v_inst_2555_, lean_object* v_x_2556_, lean_object* v_toPure_2557_, lean_object* v_inst_2558_, lean_object* v___f_2559_, lean_object* v_toBind_2560_, lean_object* v_setNextMacroScope_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_toMonadExceptOf_2567_, lean_object* v_getNextMacroScope_2568_, lean_object* v_opts_2569_){
_start:
{
lean_object* v_getCurrNamespace_2570_; lean_object* v_getOpenDecls_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; 
v_getCurrNamespace_2570_ = lean_ctor_get(v_inst_2548_, 0);
lean_inc(v_getCurrNamespace_2570_);
v_getOpenDecls_2571_ = lean_ctor_get(v_inst_2548_, 1);
lean_inc(v_getOpenDecls_2571_);
lean_dec_ref(v_inst_2548_);
lean_inc(v_toBind_2560_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2572_, 0, v_toMonadRef_2549_);
lean_closure_set(v___f_2572_, 1, v_env_2550_);
lean_closure_set(v___f_2572_, 2, v_opts_2569_);
lean_closure_set(v___f_2572_, 3, v___x_2551_);
lean_closure_set(v___f_2572_, 4, v___f_2552_);
lean_closure_set(v___f_2572_, 5, v___f_2553_);
lean_closure_set(v___f_2572_, 6, v_toMonadQuotation_2554_);
lean_closure_set(v___f_2572_, 7, v_inst_2555_);
lean_closure_set(v___f_2572_, 8, v_x_2556_);
lean_closure_set(v___f_2572_, 9, v_toPure_2557_);
lean_closure_set(v___f_2572_, 10, v_inst_2558_);
lean_closure_set(v___f_2572_, 11, v___f_2559_);
lean_closure_set(v___f_2572_, 12, v_toBind_2560_);
lean_closure_set(v___f_2572_, 13, v_setNextMacroScope_2561_);
lean_closure_set(v___f_2572_, 14, v_inst_2562_);
lean_closure_set(v___f_2572_, 15, v_inst_2563_);
lean_closure_set(v___f_2572_, 16, v_inst_2564_);
lean_closure_set(v___f_2572_, 17, v_inst_2565_);
lean_closure_set(v___f_2572_, 18, v_inst_2566_);
lean_closure_set(v___f_2572_, 19, v_toMonadExceptOf_2567_);
lean_closure_set(v___f_2572_, 20, v_getNextMacroScope_2568_);
lean_closure_set(v___f_2572_, 21, v_getOpenDecls_2571_);
v___x_2573_ = lean_apply_4(v_toBind_2560_, lean_box(0), lean_box(0), v_getCurrNamespace_2570_, v___f_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2574_ = _args[0];
lean_object* v_toMonadRef_2575_ = _args[1];
lean_object* v_env_2576_ = _args[2];
lean_object* v___x_2577_ = _args[3];
lean_object* v___f_2578_ = _args[4];
lean_object* v___f_2579_ = _args[5];
lean_object* v_toMonadQuotation_2580_ = _args[6];
lean_object* v_inst_2581_ = _args[7];
lean_object* v_x_2582_ = _args[8];
lean_object* v_toPure_2583_ = _args[9];
lean_object* v_inst_2584_ = _args[10];
lean_object* v___f_2585_ = _args[11];
lean_object* v_toBind_2586_ = _args[12];
lean_object* v_setNextMacroScope_2587_ = _args[13];
lean_object* v_inst_2588_ = _args[14];
lean_object* v_inst_2589_ = _args[15];
lean_object* v_inst_2590_ = _args[16];
lean_object* v_inst_2591_ = _args[17];
lean_object* v_inst_2592_ = _args[18];
lean_object* v_toMonadExceptOf_2593_ = _args[19];
lean_object* v_getNextMacroScope_2594_ = _args[20];
lean_object* v_opts_2595_ = _args[21];
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2574_, v_toMonadRef_2575_, v_env_2576_, v___x_2577_, v___f_2578_, v___f_2579_, v_toMonadQuotation_2580_, v_inst_2581_, v_x_2582_, v_toPure_2583_, v_inst_2584_, v___f_2585_, v_toBind_2586_, v_setNextMacroScope_2587_, v_inst_2588_, v_inst_2589_, v_inst_2590_, v_inst_2591_, v_inst_2592_, v_toMonadExceptOf_2593_, v_getNextMacroScope_2594_, v_opts_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v_inst_2597_, lean_object* v___x_2598_, lean_object* v___x_2599_, lean_object* v_inst_2600_, lean_object* v_toMonadRef_2601_, lean_object* v___x_2602_, lean_object* v_toMonadQuotation_2603_, lean_object* v_inst_2604_, lean_object* v_x_2605_, lean_object* v_toPure_2606_, lean_object* v_inst_2607_, lean_object* v___f_2608_, lean_object* v_toBind_2609_, lean_object* v_setNextMacroScope_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_toMonadExceptOf_2615_, lean_object* v_getNextMacroScope_2616_, lean_object* v_env_2617_){
_start:
{
lean_object* v_getOptions_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; 
v_getOptions_2618_ = lean_ctor_get(v_inst_2597_, 0);
lean_inc(v_getOptions_2618_);
lean_inc_ref_n(v_env_2617_, 2);
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2619_, 0, v_env_2617_);
lean_closure_set(v___f_2619_, 1, v___x_2598_);
lean_closure_set(v___f_2619_, 2, v___x_2599_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2620_, 0, v_env_2617_);
lean_inc(v_toBind_2609_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2621_, 0, v_inst_2600_);
lean_closure_set(v___f_2621_, 1, v_toMonadRef_2601_);
lean_closure_set(v___f_2621_, 2, v_env_2617_);
lean_closure_set(v___f_2621_, 3, v___x_2602_);
lean_closure_set(v___f_2621_, 4, v___f_2619_);
lean_closure_set(v___f_2621_, 5, v___f_2620_);
lean_closure_set(v___f_2621_, 6, v_toMonadQuotation_2603_);
lean_closure_set(v___f_2621_, 7, v_inst_2604_);
lean_closure_set(v___f_2621_, 8, v_x_2605_);
lean_closure_set(v___f_2621_, 9, v_toPure_2606_);
lean_closure_set(v___f_2621_, 10, v_inst_2607_);
lean_closure_set(v___f_2621_, 11, v___f_2608_);
lean_closure_set(v___f_2621_, 12, v_toBind_2609_);
lean_closure_set(v___f_2621_, 13, v_setNextMacroScope_2610_);
lean_closure_set(v___f_2621_, 14, v_inst_2611_);
lean_closure_set(v___f_2621_, 15, v_inst_2612_);
lean_closure_set(v___f_2621_, 16, v_inst_2597_);
lean_closure_set(v___f_2621_, 17, v_inst_2613_);
lean_closure_set(v___f_2621_, 18, v_inst_2614_);
lean_closure_set(v___f_2621_, 19, v_toMonadExceptOf_2615_);
lean_closure_set(v___f_2621_, 20, v_getNextMacroScope_2616_);
v___x_2622_ = lean_apply_4(v_toBind_2609_, lean_box(0), lean_box(0), v_getOptions_2618_, v___f_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_inst_2623_ = _args[0];
lean_object* v___x_2624_ = _args[1];
lean_object* v___x_2625_ = _args[2];
lean_object* v_inst_2626_ = _args[3];
lean_object* v_toMonadRef_2627_ = _args[4];
lean_object* v___x_2628_ = _args[5];
lean_object* v_toMonadQuotation_2629_ = _args[6];
lean_object* v_inst_2630_ = _args[7];
lean_object* v_x_2631_ = _args[8];
lean_object* v_toPure_2632_ = _args[9];
lean_object* v_inst_2633_ = _args[10];
lean_object* v___f_2634_ = _args[11];
lean_object* v_toBind_2635_ = _args[12];
lean_object* v_setNextMacroScope_2636_ = _args[13];
lean_object* v_inst_2637_ = _args[14];
lean_object* v_inst_2638_ = _args[15];
lean_object* v_inst_2639_ = _args[16];
lean_object* v_inst_2640_ = _args[17];
lean_object* v_toMonadExceptOf_2641_ = _args[18];
lean_object* v_getNextMacroScope_2642_ = _args[19];
lean_object* v_env_2643_ = _args[20];
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v_inst_2623_, v___x_2624_, v___x_2625_, v_inst_2626_, v_toMonadRef_2627_, v___x_2628_, v_toMonadQuotation_2629_, v_inst_2630_, v_x_2631_, v_toPure_2632_, v_inst_2633_, v___f_2634_, v_toBind_2635_, v_setNextMacroScope_2636_, v_inst_2637_, v_inst_2638_, v_inst_2639_, v_inst_2640_, v_toMonadExceptOf_2641_, v_getNextMacroScope_2642_, v_env_2643_);
return v_res_2644_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_EStateM_nonBacktrackable___redArg();
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2666_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2665_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___f_2668_; 
v___x_2667_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2668_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2668_, 0, v___x_2667_);
return v___f_2668_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___f_2670_; 
v___x_2669_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2670_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2670_, 0, v___x_2669_);
return v___f_2670_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; 
v___f_2671_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2672_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___f_2672_);
lean_ctor_set(v___x_2673_, 1, v___f_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v_toApplicative_2688_; lean_object* v_toBind_2689_; lean_object* v_getEnv_2690_; lean_object* v_toMonadExceptOf_2691_; lean_object* v_toMonadRef_2692_; lean_object* v_toMonadQuotation_2693_; lean_object* v_getNextMacroScope_2694_; lean_object* v_setNextMacroScope_2695_; lean_object* v_toPure_2696_; lean_object* v___x_2697_; lean_object* v___f_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; 
v___x_2686_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2687_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2688_ = lean_ctor_get(v_inst_2676_, 0);
v_toBind_2689_ = lean_ctor_get(v_inst_2676_, 1);
lean_inc_n(v_toBind_2689_, 3);
v_getEnv_2690_ = lean_ctor_get(v_inst_2678_, 0);
lean_inc(v_getEnv_2690_);
v_toMonadExceptOf_2691_ = lean_ctor_get(v_inst_2680_, 0);
lean_inc_ref(v_toMonadExceptOf_2691_);
v_toMonadRef_2692_ = lean_ctor_get(v_inst_2680_, 1);
lean_inc_ref_n(v_toMonadRef_2692_, 2);
v_toMonadQuotation_2693_ = lean_ctor_get(v_inst_2677_, 0);
lean_inc_ref(v_toMonadQuotation_2693_);
v_getNextMacroScope_2694_ = lean_ctor_get(v_inst_2677_, 1);
lean_inc(v_getNextMacroScope_2694_);
v_setNextMacroScope_2695_ = lean_ctor_get(v_inst_2677_, 2);
lean_inc(v_setNextMacroScope_2695_);
lean_dec_ref(v_inst_2677_);
v_toPure_2696_ = lean_ctor_get(v_toApplicative_2688_, 1);
lean_inc_n(v_toPure_2696_, 2);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2684_);
lean_inc_ref(v_inst_2676_);
lean_inc_ref(v_inst_2683_);
lean_inc_ref(v_inst_2682_);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2698_, 0, v_inst_2682_);
lean_closure_set(v___f_2698_, 1, v_inst_2683_);
lean_closure_set(v___f_2698_, 2, v_toPure_2696_);
lean_closure_set(v___f_2698_, 3, v_toBind_2689_);
lean_closure_set(v___f_2698_, 4, v_inst_2676_);
lean_closure_set(v___f_2698_, 5, v_toMonadRef_2692_);
lean_closure_set(v___f_2698_, 6, v_inst_2684_);
v___f_2699_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2699_, 0, v_inst_2683_);
lean_closure_set(v___f_2699_, 1, v___x_2687_);
lean_closure_set(v___f_2699_, 2, v___x_2697_);
lean_closure_set(v___f_2699_, 3, v_inst_2681_);
lean_closure_set(v___f_2699_, 4, v_toMonadRef_2692_);
lean_closure_set(v___f_2699_, 5, v___x_2686_);
lean_closure_set(v___f_2699_, 6, v_toMonadQuotation_2693_);
lean_closure_set(v___f_2699_, 7, v_inst_2679_);
lean_closure_set(v___f_2699_, 8, v_x_2685_);
lean_closure_set(v___f_2699_, 9, v_toPure_2696_);
lean_closure_set(v___f_2699_, 10, v_inst_2676_);
lean_closure_set(v___f_2699_, 11, v___f_2698_);
lean_closure_set(v___f_2699_, 12, v_toBind_2689_);
lean_closure_set(v___f_2699_, 13, v_setNextMacroScope_2695_);
lean_closure_set(v___f_2699_, 14, v_inst_2678_);
lean_closure_set(v___f_2699_, 15, v_inst_2682_);
lean_closure_set(v___f_2699_, 16, v_inst_2684_);
lean_closure_set(v___f_2699_, 17, v_inst_2680_);
lean_closure_set(v___f_2699_, 18, v_toMonadExceptOf_2691_);
lean_closure_set(v___f_2699_, 19, v_getNextMacroScope_2694_);
v___x_2700_ = lean_apply_4(v_toBind_2689_, lean_box(0), lean_box(0), v_getEnv_2690_, v___f_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2701_, lean_object* v_00_u03b1_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_x_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2715_, lean_object* v_00_u03b1_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_x_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Elab_liftMacroM(v_m_2715_, v_00_u03b1_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_inst_2725_, v_inst_2726_, v_x_2727_);
lean_dec(v_inst_2726_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_x_2738_, lean_object* v_stx_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_apply_1(v_x_2738_, v_stx_2739_);
v___x_2741_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v_inst_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_x_2753_, lean_object* v_stx_2754_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_apply_1(v_x_2753_, v_stx_2754_);
v___x_2756_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2743_, v_inst_2744_, v_inst_2745_, v_inst_2746_, v_inst_2747_, v_inst_2748_, v_inst_2749_, v_inst_2750_, v_inst_2751_, v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2757_, lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_x_2768_, lean_object* v_stx_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Elab_adaptMacro(v_m_2757_, v_inst_2758_, v_inst_2759_, v_inst_2760_, v_inst_2761_, v_inst_2762_, v_inst_2763_, v_inst_2764_, v_inst_2765_, v_inst_2766_, v_inst_2767_, v_x_2768_, v_stx_2769_);
lean_dec(v_inst_2767_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2771_, lean_object* v_currNamespace_2772_, lean_object* v_idx_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_name_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_inc(v_idx_2773_);
lean_inc(v_baseName_2771_);
v_name_2776_ = lean_name_append_index_after(v_baseName_2771_, v_idx_2773_);
lean_inc(v_name_2776_);
lean_inc(v_currNamespace_2772_);
v___x_2777_ = l_Lean_Name_append(v_currNamespace_2772_, v_name_2776_);
v___x_2778_ = l_Lean_Macro_hasDecl(v___x_2777_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; uint8_t v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v___x_2780_ = lean_unbox(v_a_2779_);
if (v___x_2780_ == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_idx_2773_);
lean_dec(v_currNamespace_2772_);
lean_dec(v_baseName_2771_);
v_a_2781_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2778_, 0);
lean_dec(v_unused_2789_);
v___x_2783_ = v___x_2778_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2778_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v_name_2776_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_name_2776_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec(v_name_2776_);
v_a_2790_ = lean_ctor_get(v___x_2778_, 1);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2778_, 2);
v___x_2791_ = lean_unsigned_to_nat(1u);
v___x_2792_ = lean_nat_add(v_idx_2773_, v___x_2791_);
lean_dec(v_idx_2773_);
v_idx_2773_ = v___x_2792_;
v_a_2775_ = v_a_2790_;
goto _start;
}
}
else
{
lean_object* v_a_2794_; lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_name_2776_);
lean_dec(v_idx_2773_);
lean_dec(v_currNamespace_2772_);
lean_dec(v_baseName_2771_);
v_a_2794_ = lean_ctor_get(v___x_2778_, 0);
v_a_2795_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2778_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_inc(v_a_2794_);
lean_dec(v___x_2778_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2794_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2803_, lean_object* v_currNamespace_2804_, lean_object* v_idx_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2803_, v_currNamespace_2804_, v_idx_2805_, v_a_2806_, v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Macro_getCurrNamespace(v_a_2810_, v_a_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_n(v_a_2813_, 2);
v_a_2814_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2812_, 2);
lean_inc(v_baseName_2809_);
v___x_2815_ = l_Lean_Name_append(v_a_2813_, v_baseName_2809_);
v___x_2816_ = l_Lean_Macro_hasDecl(v___x_2815_, v_a_2810_, v_a_2814_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; uint8_t v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v___x_2818_ = lean_unbox(v_a_2817_);
if (v___x_2818_ == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2813_);
v_a_2819_ = lean_ctor_get(v___x_2816_, 1);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2827_);
v___x_2821_ = v___x_2816_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2816_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_baseName_2809_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_baseName_2809_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2816_, 2);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2809_, v_a_2813_, v___x_2829_, v_a_2810_, v_a_2828_);
return v___x_2830_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2813_);
lean_dec(v_baseName_2809_);
v_a_2831_ = lean_ctor_get(v___x_2816_, 0);
v_a_2832_ = lean_ctor_get(v___x_2816_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2816_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_inc(v_a_2831_);
lean_dec(v___x_2816_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2831_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_dec(v_baseName_2809_);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2840_, v_a_2841_, v_a_2842_);
lean_dec_ref(v_a_2841_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(lean_object* v_inst_2844_, lean_object* v_name_2845_, lean_object* v_avoid_2846_, lean_object* v_env_2847_, lean_object* v_idx_2848_){
_start:
{
lean_object* v_toApplicative_2849_; lean_object* v_toPure_2850_; lean_object* v_name_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_toApplicative_2849_ = lean_ctor_get(v_inst_2844_, 0);
v_toPure_2850_ = lean_ctor_get(v_toApplicative_2849_, 1);
lean_inc(v_idx_2848_);
lean_inc(v_name_2845_);
v_name_2851_ = lean_name_append_index_after(v_name_2845_, v_idx_2848_);
lean_inc_ref(v_avoid_2846_);
lean_inc(v_name_2851_);
lean_inc_ref(v_env_2847_);
v___x_2852_ = lean_apply_2(v_avoid_2846_, v_env_2847_, v_name_2851_);
v___x_2853_ = lean_unbox(v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_inc(v_toPure_2850_);
lean_dec(v_idx_2848_);
lean_dec_ref(v_env_2847_);
lean_dec_ref(v_avoid_2846_);
lean_dec(v_name_2845_);
lean_dec_ref(v_inst_2844_);
v___x_2854_ = lean_apply_2(v_toPure_2850_, lean_box(0), v_name_2851_);
return v___x_2854_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v_name_2851_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_nat_add(v_idx_2848_, v___x_2855_);
lean_dec(v_idx_2848_);
v_idx_2848_ = v___x_2856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop(lean_object* v_m_2858_, lean_object* v_inst_2859_, lean_object* v_name_2860_, lean_object* v_avoid_2861_, lean_object* v_env_2862_, lean_object* v_idx_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(v_inst_2859_, v_name_2860_, v_avoid_2861_, v_env_2862_, v_idx_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg___lam__0(lean_object* v_avoid_2865_, lean_object* v_name_2866_, lean_object* v_toPure_2867_, lean_object* v_inst_2868_, lean_object* v_env_2869_){
_start:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_inc_ref(v_avoid_2865_);
lean_inc(v_name_2866_);
lean_inc_ref(v_env_2869_);
v___x_2870_ = lean_apply_2(v_avoid_2865_, v_env_2869_, v_name_2866_);
v___x_2871_ = lean_unbox(v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v_env_2869_);
lean_dec_ref(v_inst_2868_);
lean_dec_ref(v_avoid_2865_);
v___x_2872_ = lean_apply_2(v_toPure_2867_, lean_box(0), v_name_2866_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec(v_toPure_2867_);
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = l___private_Lean_Elab_Util_0__Lean_Elab_findUnusedName_loop___redArg(v_inst_2868_, v_name_2866_, v_avoid_2865_, v_env_2869_, v___x_2873_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName___redArg(lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_name_2877_, lean_object* v_avoid_2878_){
_start:
{
lean_object* v_toApplicative_2879_; lean_object* v_toBind_2880_; lean_object* v_getEnv_2881_; lean_object* v_toPure_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; 
v_toApplicative_2879_ = lean_ctor_get(v_inst_2875_, 0);
v_toBind_2880_ = lean_ctor_get(v_inst_2875_, 1);
lean_inc(v_toBind_2880_);
v_getEnv_2881_ = lean_ctor_get(v_inst_2876_, 0);
lean_inc(v_getEnv_2881_);
lean_dec_ref(v_inst_2876_);
v_toPure_2882_ = lean_ctor_get(v_toApplicative_2879_, 1);
lean_inc(v_toPure_2882_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_findUnusedName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2883_, 0, v_avoid_2878_);
lean_closure_set(v___f_2883_, 1, v_name_2877_);
lean_closure_set(v___f_2883_, 2, v_toPure_2882_);
lean_closure_set(v___f_2883_, 3, v_inst_2875_);
v___x_2884_ = lean_apply_4(v_toBind_2880_, lean_box(0), lean_box(0), v_getEnv_2881_, v___f_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findUnusedName(lean_object* v_m_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_name_2888_, lean_object* v_avoid_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Elab_findUnusedName___redArg(v_inst_2886_, v_inst_2887_, v_name_2888_, v_avoid_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2893_ = l_Lean_stringToMessageData(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_name_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2899_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2900_ = l_Lean_MessageData_ofName(v_name_2898_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_logError___redArg(v_inst_2894_, v_inst_2895_, v_inst_2896_, v_inst_2897_, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_ex_2908_){
_start:
{
lean_object* v_toApplicative_2909_; lean_object* v_toBind_2910_; lean_object* v_toPure_2911_; 
v_toApplicative_2909_ = lean_ctor_get(v_inst_2903_, 0);
v_toBind_2910_ = lean_ctor_get(v_inst_2903_, 1);
v_toPure_2911_ = lean_ctor_get(v_toApplicative_2909_, 1);
if (lean_obj_tag(v_ex_2908_) == 0)
{
lean_object* v_ref_2915_; lean_object* v_msg_2916_; lean_object* v___x_2917_; 
lean_dec(v_inst_2907_);
v_ref_2915_ = lean_ctor_get(v_ex_2908_, 0);
lean_inc(v_ref_2915_);
v_msg_2916_ = lean_ctor_get(v_ex_2908_, 1);
lean_inc_ref(v_msg_2916_);
lean_dec_ref_known(v_ex_2908_, 2);
v___x_2917_ = l_Lean_logErrorAt___redArg(v_inst_2903_, v_inst_2904_, v_inst_2905_, v_inst_2906_, v_ref_2915_, v_msg_2916_);
return v___x_2917_;
}
else
{
lean_object* v_id_2918_; uint8_t v___x_2919_; 
lean_inc(v_toBind_2910_);
v_id_2918_ = lean_ctor_get(v_ex_2908_, 0);
lean_inc(v_id_2918_);
v___x_2919_ = l_Lean_Elab_isAbortExceptionId(v_id_2918_);
if (v___x_2919_ == 0)
{
uint8_t v___x_2920_; 
v___x_2920_ = l_Lean_Exception_isInterrupt(v_ex_2908_);
lean_dec_ref_known(v_ex_2908_, 2);
if (v___x_2920_ == 0)
{
lean_object* v___f_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2921_, 0, v_inst_2903_);
lean_closure_set(v___f_2921_, 1, v_inst_2904_);
lean_closure_set(v___f_2921_, 2, v_inst_2905_);
lean_closure_set(v___f_2921_, 3, v_inst_2906_);
v___x_2922_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2922_, 0, v_id_2918_);
v___x_2923_ = lean_apply_2(v_inst_2907_, lean_box(0), v___x_2922_);
v___x_2924_ = lean_apply_4(v_toBind_2910_, lean_box(0), lean_box(0), v___x_2923_, v___f_2921_);
return v___x_2924_;
}
else
{
lean_inc(v_toPure_2911_);
lean_dec(v_id_2918_);
lean_dec(v_toBind_2910_);
lean_dec(v_inst_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_inst_2905_);
lean_dec_ref(v_inst_2904_);
lean_dec_ref(v_inst_2903_);
goto v___jp_2912_;
}
}
else
{
lean_inc(v_toPure_2911_);
lean_dec(v_id_2918_);
lean_dec_ref_known(v_ex_2908_, 2);
lean_dec(v_toBind_2910_);
lean_dec(v_inst_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_inst_2905_);
lean_dec_ref(v_inst_2904_);
lean_dec_ref(v_inst_2903_);
goto v___jp_2912_;
}
}
v___jp_2912_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_box(0);
v___x_2914_ = lean_apply_2(v_toPure_2911_, lean_box(0), v___x_2913_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_ex_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Elab_logException___redArg(v_inst_2926_, v_inst_2927_, v_inst_2928_, v_inst_2929_, v_inst_2930_, v_ex_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_ex_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Elab_logException___redArg(v_inst_2933_, v_inst_2934_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_ex_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_x_2946_){
_start:
{
lean_object* v_tryCatch_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; 
v_tryCatch_2947_ = lean_ctor_get(v_inst_2942_, 1);
lean_inc(v_tryCatch_2947_);
lean_dec_ref(v_inst_2942_);
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2948_, 0, v_inst_2940_);
lean_closure_set(v___f_2948_, 1, v_inst_2941_);
lean_closure_set(v___f_2948_, 2, v_inst_2943_);
lean_closure_set(v___f_2948_, 3, v_inst_2944_);
lean_closure_set(v___f_2948_, 4, v_inst_2945_);
v___x_2949_ = lean_apply_3(v_tryCatch_2947_, lean_box(0), v_x_2946_, v___f_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2950_, lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Elab_withLogging___redArg(v_inst_2951_, v_inst_2952_, v_inst_2953_, v_inst_2954_, v_inst_2955_, v_inst_2956_, v_x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2961_ = l_Lean_stringToMessageData(v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2962_, lean_object* v_ex_2963_, lean_object* v_toPure_2964_, lean_object* v_____do__lift_2965_){
_start:
{
lean_object* v_exPosition_2966_; lean_object* v_line_2967_; lean_object* v_column_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2988_; 
v_exPosition_2966_ = l_Lean_FileMap_toPosition(v_____do__lift_2965_, v_val_2962_);
v_line_2967_ = lean_ctor_get(v_exPosition_2966_, 0);
v_column_2968_ = lean_ctor_get(v_exPosition_2966_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_exPosition_2966_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2970_ = v_exPosition_2966_;
v_isShared_2971_ = v_isSharedCheck_2988_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_column_2968_);
lean_inc(v_line_2967_);
lean_dec(v_exPosition_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2988_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2972_ = l_Nat_reprFast(v_line_2967_);
v___x_2973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
v___x_2974_ = l_Lean_MessageData_ofFormat(v___x_2973_);
v___x_2975_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 7);
lean_ctor_set(v___x_2970_, 1, v___x_2975_);
lean_ctor_set(v___x_2970_, 0, v___x_2974_);
v___x_2977_ = v___x_2970_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2978_ = l_Nat_reprFast(v_column_2968_);
v___x_2979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
v___x_2980_ = l_Lean_MessageData_ofFormat(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2977_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = l_Lean_Exception_toMessageData(v_ex_2963_);
v___x_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = lean_apply_2(v_toPure_2964_, lean_box(0), v___x_2985_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2989_, lean_object* v_ex_2990_, lean_object* v_toPure_2991_, lean_object* v_____do__lift_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2989_, v_ex_2990_, v_toPure_2991_, v_____do__lift_2992_);
lean_dec(v_val_2989_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2994_, lean_object* v_toPure_2995_, lean_object* v_toBind_2996_, lean_object* v_toMonadFileMap_2997_, lean_object* v_pos_2998_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = l_Lean_Exception_getRef(v_ex_2994_);
v___x_3000_ = 0;
v___x_3001_ = l_Lean_Syntax_getPos_x3f(v___x_2999_, v___x_3000_);
lean_dec(v___x_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v_toMonadFileMap_2997_);
lean_dec(v_toBind_2996_);
v___x_3002_ = l_Lean_Exception_toMessageData(v_ex_2994_);
v___x_3003_ = lean_apply_2(v_toPure_2995_, lean_box(0), v___x_3002_);
return v___x_3003_;
}
else
{
lean_object* v_val_3004_; uint8_t v_decide_3005_; 
v_val_3004_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3001_, 1);
v_decide_3005_ = lean_nat_dec_eq(v_pos_2998_, v_val_3004_);
if (v_decide_3005_ == 0)
{
lean_object* v___f_3006_; lean_object* v___x_3007_; 
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3006_, 0, v_val_3004_);
lean_closure_set(v___f_3006_, 1, v_ex_2994_);
lean_closure_set(v___f_3006_, 2, v_toPure_2995_);
v___x_3007_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v_toMonadFileMap_2997_, v___f_3006_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v_val_3004_);
lean_dec(v_toMonadFileMap_2997_);
lean_dec(v_toBind_2996_);
v___x_3008_ = l_Lean_Exception_toMessageData(v_ex_2994_);
v___x_3009_ = lean_apply_2(v_toPure_2995_, lean_box(0), v___x_3008_);
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_3010_, lean_object* v_toPure_3011_, lean_object* v_toBind_3012_, lean_object* v_toMonadFileMap_3013_, lean_object* v_pos_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_3010_, v_toPure_3011_, v_toBind_3012_, v_toMonadFileMap_3013_, v_pos_3014_);
lean_dec(v_pos_3014_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_ex_3018_){
_start:
{
lean_object* v_toApplicative_3019_; lean_object* v_toBind_3020_; lean_object* v_toPure_3021_; lean_object* v_toMonadFileMap_3022_; lean_object* v___x_3023_; lean_object* v___f_3024_; lean_object* v___x_3025_; 
v_toApplicative_3019_ = lean_ctor_get(v_inst_3016_, 0);
v_toBind_3020_ = lean_ctor_get(v_inst_3016_, 1);
lean_inc_n(v_toBind_3020_, 2);
v_toPure_3021_ = lean_ctor_get(v_toApplicative_3019_, 1);
lean_inc(v_toPure_3021_);
v_toMonadFileMap_3022_ = lean_ctor_get(v_inst_3017_, 0);
lean_inc(v_toMonadFileMap_3022_);
v___x_3023_ = l_Lean_getRefPos___redArg(v_inst_3016_, v_inst_3017_);
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3024_, 0, v_ex_3018_);
lean_closure_set(v___f_3024_, 1, v_toPure_3021_);
lean_closure_set(v___f_3024_, 2, v_toBind_3020_);
lean_closure_set(v___f_3024_, 3, v_toMonadFileMap_3022_);
v___x_3025_ = lean_apply_4(v_toBind_3020_, lean_box(0), lean_box(0), v___x_3023_, v___f_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_ex_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3027_, v_inst_3028_, v_ex_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_x_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3031_, v_inst_3032_, v_x_3033_);
return v___x_3034_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_____do__lift_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3042_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_msg_3038_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_toMessageList(v_____do__lift_3041_);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_throwError___redArg(v_inst_3039_, v_inst_3040_, v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_msg_3050_, lean_object* v_exs_3051_){
_start:
{
lean_object* v_toBind_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; size_t v_sz_3055_; size_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_toBind_3052_ = lean_ctor_get(v_inst_3048_, 1);
lean_inc(v_toBind_3052_);
lean_inc_ref_n(v_inst_3048_, 2);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3053_, 0, v_inst_3048_);
lean_closure_set(v___f_3053_, 1, v_inst_3049_);
v___f_3054_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3054_, 0, v_msg_3050_);
lean_closure_set(v___f_3054_, 1, v_inst_3048_);
lean_closure_set(v___f_3054_, 2, v_inst_3047_);
v_sz_3055_ = lean_array_size(v_exs_3051_);
v___x_3056_ = ((size_t)0ULL);
v___x_3057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3048_, v___f_3053_, v_sz_3055_, v___x_3056_, v_exs_3051_);
v___x_3058_ = lean_apply_4(v_toBind_3052_, lean_box(0), lean_box(0), v___x_3057_, v___f_3054_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_3059_, lean_object* v_00_u03b1_3060_, lean_object* v_inst_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_msg_3064_, lean_object* v_exs_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_3061_, v_inst_3062_, v_inst_3063_, v_msg_3064_, v_exs_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3134_ = 0;
v___x_3135_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3136_ = l_Lean_registerTraceClass(v___x_3133_, v___x_3134_, v___x_3135_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec_ref_known(v___x_3136_, 1);
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3138_ = l_Lean_registerTraceClass(v___x_3137_, v___x_3134_, v___x_3135_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; 
lean_dec_ref_known(v___x_3138_, 1);
v___x_3139_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3140_ = 1;
v___x_3141_ = l_Lean_registerTraceClass(v___x_3139_, v___x_3140_, v___x_3135_);
return v___x_3141_;
}
else
{
return v___x_3138_;
}
}
else
{
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3143_;
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
