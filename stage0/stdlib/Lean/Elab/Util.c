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
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
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
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(lean_object* v_x_30_, lean_object* v_x_31_){
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
LEAN_EXPORT void l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
uint8_t v_res_41_;
v_res_41_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_x_30_, v_x_31_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0___boxed(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_x_42_, v_x_43_);
lean_dec(v_x_43_);
lean_dec(v_x_42_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
uint8_t l_Lean_MacroScopesView_equalScope(lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
lean_object* v_imported_48_; lean_object* v_ctx_49_; lean_object* v_scopes_50_; lean_object* v_imported_51_; lean_object* v_ctx_52_; lean_object* v_scopes_53_; uint8_t v___y_55_; uint8_t v___x_57_; 
v_imported_48_ = lean_ctor_get(v_a_46_, 1);
v_ctx_49_ = lean_ctor_get(v_a_46_, 2);
v_scopes_50_ = lean_ctor_get(v_a_46_, 3);
v_imported_51_ = lean_ctor_get(v_b_47_, 1);
v_ctx_52_ = lean_ctor_get(v_b_47_, 2);
v_scopes_53_ = lean_ctor_get(v_b_47_, 3);
v___x_57_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_scopes_50_, v_scopes_53_);
if (v___x_57_ == 0)
{
v___y_55_ = v___x_57_;
goto v___jp_54_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = lean_name_eq(v_ctx_49_, v_ctx_52_);
v___y_55_ = v___x_58_;
goto v___jp_54_;
}
v___jp_54_:
{
if (v___y_55_ == 0)
{
return v___y_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = lean_name_eq(v_imported_48_, v_imported_51_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT void l_Lean_MacroScopesView_equalScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_46_ = stack[0].m_obj;
lean_object* v_b_47_ = stack[1].m_obj;
uint8_t v_res_59_;
v_res_59_ = l_Lean_MacroScopesView_equalScope(v_a_46_, v_b_47_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_equalScope___boxed(lean_object* v_a_60_, lean_object* v_b_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lean_MacroScopesView_equalScope(v_a_60_, v_b_61_);
lean_dec_ref(v_b_61_);
lean_dec_ref(v_a_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object* v_stx_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_Syntax_isNone(v_stx_73_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_Lean_Syntax_getArg(v_stx_73_, v___x_77_);
v___x_79_ = ((lean_object*)(l_Lean_Elab_expandOptNamedPrio___closed__4));
lean_inc(v___x_78_);
v___x_80_ = l_Lean_Syntax_isOfKind(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec(v___x_78_);
v___x_81_ = l_Lean_Macro_throwUnsupported___redArg(v_a_75_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(3u);
v___x_83_ = l_Lean_Syntax_getArg(v___x_78_, v___x_82_);
lean_dec(v___x_78_);
v___x_84_ = l_Lean_evalPrio(v___x_83_, v_a_74_, v_a_75_);
return v___x_84_;
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1000u);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_75_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object* v_stx_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_expandOptNamedPrio(v_stx_87_, v_a_88_, v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_stx_87_);
return v_res_90_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
if (lean_obj_tag(v_x_92_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 1;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
else
{
if (lean_obj_tag(v_x_92_) == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v_val_97_; uint8_t v_decide_98_; 
v_val_96_ = lean_ctor_get(v_x_91_, 0);
v_val_97_ = lean_ctor_get(v_x_92_, 0);
v_decide_98_ = lean_nat_dec_eq(v_val_96_, v_val_97_);
return v_decide_98_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_91_ = stack[0].m_obj;
lean_object* v_x_92_ = stack[1].m_obj;
uint8_t v_res_99_;
v_res_99_ = l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_91_, v_x_92_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_100_, v_x_101_);
lean_dec(v_x_101_);
lean_dec(v_x_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(lean_object* v___x_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
lean_object* v_head_107_; lean_object* v_tail_108_; lean_object* v_before_109_; uint8_t v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_head_107_ = lean_ctor_get(v_x_105_, 0);
v_tail_108_ = lean_ctor_get(v_x_105_, 1);
v_before_109_ = lean_ctor_get(v_head_107_, 0);
v___x_110_ = 0;
v___x_111_ = l_Lean_Syntax_getPos_x3f(v_before_109_, v___x_110_);
v___x_112_ = l_instBEqOption_beq___at___00Lean_Elab_getBetterRef_spec__0(v___x_111_, v___x_104_);
lean_dec(v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
lean_inc(v_head_107_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_head_107_);
return v___x_113_;
}
else
{
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(lean_object* v___x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec(v___x_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* v_ref_118_, lean_object* v_macroStack_119_){
_start:
{
uint8_t v___x_120_; lean_object* v___x_121_; 
v___x_120_ = 0;
v___x_121_ = l_Lean_Syntax_getPos_x3f(v_ref_118_, v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
v___x_122_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_121_, v_macroStack_119_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_inc(v_ref_118_);
return v_ref_118_;
}
else
{
lean_object* v_val_123_; lean_object* v_before_124_; 
v_val_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_122_, 1);
v_before_124_ = lean_ctor_get(v_val_123_, 0);
lean_inc(v_before_124_);
lean_dec(v_val_123_);
return v_before_124_;
}
}
else
{
lean_dec_ref_known(v___x_121_, 1);
lean_inc(v_ref_118_);
return v_ref_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* v_ref_125_, lean_object* v_macroStack_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Elab_getBetterRef(v_ref_125_, v_macroStack_126_);
lean_dec(v_macroStack_126_);
lean_dec(v_ref_125_);
return v_res_127_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object* v_name_128_, lean_object* v_decl_129_, lean_object* v_ref_130_){
_start:
{
lean_object* v_defValue_132_; lean_object* v_descr_133_; lean_object* v_deprecation_x3f_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_defValue_132_ = lean_ctor_get(v_decl_129_, 0);
v_descr_133_ = lean_ctor_get(v_decl_129_, 1);
v_deprecation_x3f_134_ = lean_ctor_get(v_decl_129_, 2);
v___x_135_ = lean_alloc_ctor(1, 0, 1);
v___x_136_ = lean_unbox(v_defValue_132_);
lean_ctor_set_uint8(v___x_135_, 0, v___x_136_);
lean_inc(v_deprecation_x3f_134_);
lean_inc_ref(v_descr_133_);
lean_inc_n(v_name_128_, 2);
v___x_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_137_, 0, v_name_128_);
lean_ctor_set(v___x_137_, 1, v_ref_130_);
lean_ctor_set(v___x_137_, 2, v___x_135_);
lean_ctor_set(v___x_137_, 3, v_descr_133_);
lean_ctor_set(v___x_137_, 4, v_deprecation_x3f_134_);
v___x_138_ = lean_register_option(v_name_128_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v___x_138_, 0);
lean_dec(v_unused_147_);
v___x_140_ = v___x_138_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_dec(v___x_138_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc(v_defValue_132_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_name_128_);
lean_ctor_set(v___x_142_, 1, v_defValue_132_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_name_128_);
v_a_148_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_138_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_128_ = stack[0].m_obj;
lean_object* v_decl_129_ = stack[1].m_obj;
lean_object* v_ref_130_ = stack[2].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_128_, v_decl_129_, v_ref_130_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_157_, lean_object* v_decl_158_, lean_object* v_ref_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_157_, v_decl_158_, v_ref_159_);
lean_dec_ref(v_decl_158_);
return v_res_161_;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_182_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_183_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_180_, v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_184_;
v_res_184_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1));
v___x_191_ = l_Lean_MessageData_ofFormat(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0(lean_object* v___x_192_, lean_object* v_msgData_193_, lean_object* v_elem_194_){
_start:
{
lean_object* v_before_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_207_; 
v_before_195_ = lean_ctor_get(v_elem_194_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_elem_194_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_elem_194_, 1);
lean_dec(v_unused_208_);
v___x_197_ = v_elem_194_;
v_isShared_198_ = v_isSharedCheck_207_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_before_195_);
lean_dec(v_elem_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_207_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 7);
lean_ctor_set(v___x_197_, 1, v___x_192_);
lean_ctor_set(v___x_197_, 0, v_msgData_193_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_msgData_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_192_);
v___x_200_ = v_reuseFailAlloc_206_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2, &l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2);
v___x_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_MessageData_ofSyntax(v_before_195_);
v___x_204_ = l_Lean_indentD(v___x_203_);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_202_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
return v___x_205_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(1);
v___x_210_ = l_Lean_MessageData_ofFormat(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___f_212_; 
v___x_211_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__0), 3, 1);
lean_closure_set(v___f_212_, 0, v___x_211_);
return v___f_212_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3));
v___x_217_ = l_Lean_MessageData_ofFormat(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_218_, lean_object* v_toPure_219_, lean_object* v_msgData_220_, lean_object* v_macroStack_221_, lean_object* v_____do__lift_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = l_Lean_Elab_pp_macroStack;
v___x_224_ = l_Lean_Option_get___redArg(v___x_218_, v_____do__lift_222_, v___x_223_);
v___x_225_ = lean_unbox(v___x_224_);
lean_dec(v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec(v_macroStack_221_);
v___x_226_ = lean_apply_2(v_toPure_219_, lean_box(0), v_msgData_220_);
return v___x_226_;
}
else
{
if (lean_obj_tag(v_macroStack_221_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_apply_2(v_toPure_219_, lean_box(0), v_msgData_220_);
return v___x_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_after_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_245_; 
v_head_228_ = lean_ctor_get(v_macroStack_221_, 0);
lean_inc(v_head_228_);
v_after_229_ = lean_ctor_get(v_head_228_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_head_228_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_head_228_, 0);
lean_dec(v_unused_246_);
v___x_231_ = v_head_228_;
v_isShared_232_ = v_isSharedCheck_245_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_after_229_);
lean_dec(v_head_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_245_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_234_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 7);
lean_ctor_set(v___x_231_, 1, v___x_233_);
lean_ctor_set(v___x_231_, 0, v_msgData_220_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_msgData_220_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_233_);
v___x_236_ = v_reuseFailAlloc_244_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_msgData_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_237_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_MessageData_ofSyntax(v_after_229_);
v___x_240_ = l_Lean_indentD(v___x_239_);
v_msgData_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_241_, 0, v___x_238_);
lean_ctor_set(v_msgData_241_, 1, v___x_240_);
v___x_242_ = l_List_foldl___redArg(v___f_234_, v_msgData_241_, v_macroStack_221_);
v___x_243_ = lean_apply_2(v_toPure_219_, lean_box(0), v___x_242_);
return v___x_243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_247_, lean_object* v_toPure_248_, lean_object* v_msgData_249_, lean_object* v_macroStack_250_, lean_object* v_____do__lift_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_247_, v_toPure_248_, v_msgData_249_, v_macroStack_250_, v_____do__lift_251_);
lean_dec_ref(v_____do__lift_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_msgData_255_, lean_object* v_macroStack_256_){
_start:
{
lean_object* v___x_257_; lean_object* v_toApplicative_258_; lean_object* v_toBind_259_; lean_object* v_getOptions_260_; lean_object* v_toPure_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v___x_257_ = l_Lean_KVMap_instValueBool;
v_toApplicative_258_ = lean_ctor_get(v_inst_253_, 0);
lean_inc_ref(v_toApplicative_258_);
v_toBind_259_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_259_);
lean_dec_ref(v_inst_253_);
v_getOptions_260_ = lean_ctor_get(v_inst_254_, 0);
lean_inc(v_getOptions_260_);
lean_dec_ref(v_inst_254_);
v_toPure_261_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_261_);
lean_dec_ref(v_toApplicative_258_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_262_, 0, v___x_257_);
lean_closure_set(v___f_262_, 1, v_toPure_261_);
lean_closure_set(v___f_262_, 2, v_msgData_255_);
lean_closure_set(v___f_262_, 3, v_macroStack_256_);
v___x_263_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v_getOptions_260_, v___f_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_msgData_267_, lean_object* v_macroStack_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Elab_addMacroStack___redArg(v_inst_265_, v_inst_266_, v_msgData_267_, v_macroStack_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_____r_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_277_ = l_Lean_throwError___redArg(v_inst_273_, v_inst_274_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_278_, lean_object* v___f_279_, lean_object* v_toPure_280_, lean_object* v_____do__lift_281_){
_start:
{
uint8_t v___x_282_; 
lean_inc(v_k_278_);
v___x_282_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_281_, v_k_278_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_toPure_280_);
lean_dec(v_k_278_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_1(v___f_279_, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v___f_279_);
v___x_285_ = lean_apply_2(v_toPure_280_, lean_box(0), v_k_278_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_286_, lean_object* v___f_287_, lean_object* v_toPure_288_, lean_object* v_toBind_289_, lean_object* v_getEnv_290_, lean_object* v_____do__lift_291_){
_start:
{
lean_object* v_k_292_; lean_object* v___f_293_; lean_object* v___x_294_; 
v_k_292_ = l_Lean_mkPrivateName(v_____do__lift_291_, v_k_286_);
v___f_293_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_293_, 0, v_k_292_);
lean_closure_set(v___f_293_, 1, v___f_287_);
lean_closure_set(v___f_293_, 2, v_toPure_288_);
v___x_294_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v_getEnv_290_, v___f_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_295_, lean_object* v___f_296_, lean_object* v_toPure_297_, lean_object* v_toBind_298_, lean_object* v_getEnv_299_, lean_object* v_____do__lift_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_295_, v___f_296_, v_toPure_297_, v_toBind_298_, v_getEnv_299_, v_____do__lift_300_);
lean_dec_ref(v_____do__lift_300_);
return v_res_301_;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_302_, lean_object* v_toBind_303_, lean_object* v_getEnv_304_, lean_object* v___f_305_, lean_object* v_k_306_, uint8_t v___x_307_, lean_object* v_____do__lift_308_){
_start:
{
uint8_t v_isExporting_316_; 
v_isExporting_316_ = lean_ctor_get_uint8(v_____do__lift_308_, sizeof(void*)*13);
if (v_isExporting_316_ == 0)
{
goto v___jp_312_;
}
else
{
if (v___x_307_ == 0)
{
lean_dec(v___f_305_);
lean_dec(v_getEnv_304_);
lean_dec(v_toBind_303_);
goto v___jp_309_;
}
else
{
goto v___jp_312_;
}
}
v___jp_309_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v___f_302_, v___x_310_);
return v___x_311_;
}
v___jp_312_:
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_isPrivateName(v_k_306_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec(v___f_302_);
v___x_314_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v_getEnv_304_, v___f_305_);
return v___x_314_;
}
else
{
if (v___x_307_ == 0)
{
lean_dec(v___f_305_);
lean_dec(v_getEnv_304_);
lean_dec(v_toBind_303_);
goto v___jp_309_;
}
else
{
lean_object* v___x_315_; 
lean_dec(v___f_302_);
v___x_315_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v_getEnv_304_, v___f_305_);
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_302_ = stack[0].m_obj;
lean_object* v_toBind_303_ = stack[1].m_obj;
lean_object* v_getEnv_304_ = stack[2].m_obj;
lean_object* v___f_305_ = stack[3].m_obj;
lean_object* v_k_306_ = stack[4].m_obj;
uint8_t v___x_307_ = stack[5].m_num;
lean_object* v_____do__lift_308_ = stack[6].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_302_, v_toBind_303_, v_getEnv_304_, v___f_305_, v_k_306_, v___x_307_, v_____do__lift_308_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_318_, lean_object* v_toBind_319_, lean_object* v_getEnv_320_, lean_object* v___f_321_, lean_object* v_k_322_, lean_object* v___x_323_, lean_object* v_____do__lift_324_){
_start:
{
uint8_t v___x_228__boxed_325_; lean_object* v_res_326_; 
v___x_228__boxed_325_ = lean_unbox(v___x_323_);
v_res_326_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_318_, v_toBind_319_, v_getEnv_320_, v___f_321_, v_k_322_, v___x_228__boxed_325_, v_____do__lift_324_);
lean_dec_ref(v_____do__lift_324_);
lean_dec(v_k_322_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_327_, lean_object* v___f_328_, lean_object* v_toBind_329_, lean_object* v_getEnv_330_, lean_object* v___f_331_, lean_object* v_toPure_332_, lean_object* v_____do__lift_333_){
_start:
{
uint8_t v___x_334_; 
lean_inc(v_k_327_);
v___x_334_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_333_, v_k_327_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
lean_dec(v_toPure_332_);
v___x_335_ = lean_box(v___x_334_);
lean_inc(v_getEnv_330_);
lean_inc(v_toBind_329_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_336_, 0, v___f_328_);
lean_closure_set(v___f_336_, 1, v_toBind_329_);
lean_closure_set(v___f_336_, 2, v_getEnv_330_);
lean_closure_set(v___f_336_, 3, v___f_331_);
lean_closure_set(v___f_336_, 4, v_k_327_);
lean_closure_set(v___f_336_, 5, v___x_335_);
v___x_337_ = lean_apply_4(v_toBind_329_, lean_box(0), lean_box(0), v_getEnv_330_, v___f_336_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; 
lean_dec(v___f_331_);
lean_dec(v_getEnv_330_);
lean_dec(v_toBind_329_);
lean_dec(v___f_328_);
v___x_338_ = lean_apply_2(v_toPure_332_, lean_box(0), v_k_327_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_k_342_){
_start:
{
lean_object* v_toApplicative_343_; lean_object* v_toBind_344_; lean_object* v_getEnv_345_; lean_object* v_toPure_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; 
v_toApplicative_343_ = lean_ctor_get(v_inst_339_, 0);
v_toBind_344_ = lean_ctor_get(v_inst_339_, 1);
lean_inc_n(v_toBind_344_, 3);
v_getEnv_345_ = lean_ctor_get(v_inst_340_, 0);
lean_inc_n(v_getEnv_345_, 3);
lean_dec_ref(v_inst_340_);
v_toPure_346_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc_n(v_toPure_346_, 2);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_347_, 0, v_inst_339_);
lean_closure_set(v___f_347_, 1, v_inst_341_);
lean_inc_ref(v___f_347_);
lean_inc(v_k_342_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_348_, 0, v_k_342_);
lean_closure_set(v___f_348_, 1, v___f_347_);
lean_closure_set(v___f_348_, 2, v_toPure_346_);
lean_closure_set(v___f_348_, 3, v_toBind_344_);
lean_closure_set(v___f_348_, 4, v_getEnv_345_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_349_, 0, v_k_342_);
lean_closure_set(v___f_349_, 1, v___f_347_);
lean_closure_set(v___f_349_, 2, v_toBind_344_);
lean_closure_set(v___f_349_, 3, v_getEnv_345_);
lean_closure_set(v___f_349_, 4, v___f_348_);
lean_closure_set(v___f_349_, 5, v_toPure_346_);
v___x_350_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v_getEnv_345_, v___f_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_k_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_352_, v_inst_353_, v_inst_354_, v_k_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_k_360_, lean_object* v_pre_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_357_, v_inst_358_, v_inst_359_, v_k_360_, v_pre_361_, v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_k_367_, lean_object* v_x_368_){
_start:
{
switch(lean_obj_tag(v_x_368_))
{
case 1:
{
lean_object* v_toMonadExceptOf_369_; lean_object* v_pre_370_; lean_object* v_tryCatch_371_; lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_toMonadExceptOf_369_ = lean_ctor_get(v_inst_366_, 0);
v_pre_370_ = lean_ctor_get(v_x_368_, 0);
v_tryCatch_371_ = lean_ctor_get(v_toMonadExceptOf_369_, 1);
lean_inc(v_tryCatch_371_);
lean_inc(v_pre_370_);
lean_inc(v_k_367_);
lean_inc_ref(v_inst_366_);
lean_inc_ref(v_inst_365_);
lean_inc_ref(v_inst_364_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_372_, 0, v_inst_364_);
lean_closure_set(v___f_372_, 1, v_inst_365_);
lean_closure_set(v___f_372_, 2, v_inst_366_);
lean_closure_set(v___f_372_, 3, v_k_367_);
lean_closure_set(v___f_372_, 4, v_pre_370_);
v___x_373_ = l_Lean_Name_append(v_x_368_, v_k_367_);
v___x_374_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_364_, v_inst_365_, v_inst_366_, v___x_373_);
v___x_375_ = lean_apply_3(v_tryCatch_371_, lean_box(0), v___x_374_, v___f_372_);
return v___x_375_;
}
case 0:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_364_, v_inst_365_, v_inst_366_, v_k_367_);
return v___x_376_;
}
default: 
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_x_368_);
lean_dec(v_k_367_);
lean_dec_ref(v_inst_365_);
v___x_377_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_378_ = l_Lean_throwError___redArg(v_inst_364_, v_inst_366_, v___x_377_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_k_382_, lean_object* v_pre_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_379_, v_inst_380_, v_inst_381_, v_k_382_, v_pre_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_k_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_387_, v_inst_388_, v_inst_389_, v_k_390_, v_x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_393_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_ctor_set(v___x_399_, 3, v___x_398_);
lean_ctor_set(v___x_399_, 4, v___x_397_);
lean_ctor_set(v___x_399_, 5, v___x_397_);
lean_ctor_set(v___x_399_, 6, v___x_397_);
lean_ctor_set(v___x_399_, 7, v___x_397_);
lean_ctor_set(v___x_399_, 8, v___x_397_);
lean_ctor_set(v___x_399_, 9, v___x_397_);
lean_ctor_set(v___x_399_, 10, v___x_397_);
lean_ctor_set(v___x_399_, 11, v___x_396_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((size_t)5ULL);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_unsigned_to_nat(32u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_408_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_404_);
lean_ctor_set(v___x_408_, 3, v___x_404_);
lean_ctor_set_usize(v___x_408_, 4, v___x_403_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_box(1);
v___x_410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_411_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_toCold_418_; lean_object* v_env_419_; lean_object* v_options_420_; uint8_t v___x_421_; lean_object* v_env_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_toCold_418_ = lean_ctor_get(v___y_414_, 0);
v_env_419_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_env_419_);
lean_dec(v___x_417_);
v_options_420_ = lean_ctor_get(v_toCold_418_, 2);
v___x_421_ = 0;
v_env_422_ = l_Lean_Environment_setRecordingDeps(v_env_419_, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_424_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_420_);
v___x_425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_425_, 0, v_env_422_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_ctor_set(v___x_425_, 3, v_options_420_);
v___x_426_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_msgData_413_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_413_ = stack[0].m_obj;
lean_object* v___y_414_ = stack[1].m_obj;
lean_object* v___y_415_ = stack[2].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_413_, v___y_414_, v___y_415_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_433_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_ref_438_; lean_object* v___x_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_ref_438_ = lean_ctor_get(v___y_435_, 2);
v___x_439_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_434_, v___y_435_, v___y_436_);
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
lean_inc(v_ref_438_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_ref_438_);
lean_ctor_set(v___x_444_, 1, v_a_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 1);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_434_ = stack[0].m_obj;
lean_object* v___y_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_434_, v___y_435_, v___y_436_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_454_;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_464_; lean_object* v_env_465_; uint8_t v___x_466_; 
v___x_464_ = lean_st_ref_get(v___y_457_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_464_);
lean_inc(v_k_455_);
v___x_466_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_465_, v_k_455_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___y_469_; lean_object* v_env_486_; uint8_t v_isExporting_487_; 
v___x_467_ = lean_st_ref_get(v___y_457_);
v_env_486_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_467_);
v_isExporting_487_ = lean_ctor_get_uint8(v_env_486_, sizeof(void*)*13);
lean_dec_ref(v_env_486_);
if (v_isExporting_487_ == 0)
{
goto v___jp_477_;
}
else
{
if (v___x_466_ == 0)
{
v___y_469_ = v___x_466_;
goto v___jp_468_;
}
else
{
goto v___jp_477_;
}
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
lean_dec(v_k_455_);
v___y_460_ = v___y_456_;
v___y_461_ = v___y_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_470_; lean_object* v_env_471_; lean_object* v_k_472_; lean_object* v___x_473_; lean_object* v_env_474_; uint8_t v___x_475_; 
v___x_470_ = lean_st_ref_get(v___y_457_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref(v_env_471_);
lean_dec(v___x_470_);
v_k_472_ = l_Lean_mkPrivateName(v_env_471_, v_k_455_);
lean_dec_ref(v_env_471_);
v___x_473_ = lean_st_ref_get(v___y_457_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_473_);
lean_inc(v_k_472_);
v___x_475_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_474_, v_k_472_);
if (v___x_475_ == 0)
{
lean_dec(v_k_472_);
v___y_460_ = v___y_456_;
v___y_461_ = v___y_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_k_472_);
return v___x_476_;
}
}
}
v___jp_477_:
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_isPrivateName(v_k_455_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_env_480_; lean_object* v_k_481_; lean_object* v___x_482_; lean_object* v_env_483_; uint8_t v___x_484_; 
v___x_479_ = lean_st_ref_get(v___y_457_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_env_480_);
lean_dec(v___x_479_);
v_k_481_ = l_Lean_mkPrivateName(v_env_480_, v_k_455_);
lean_dec_ref(v_env_480_);
v___x_482_ = lean_st_ref_get(v___y_457_);
v_env_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_env_483_);
lean_dec(v___x_482_);
lean_inc(v_k_481_);
v___x_484_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_483_, v_k_481_);
if (v___x_484_ == 0)
{
lean_dec(v_k_481_);
v___y_460_ = v___y_456_;
v___y_461_ = v___y_457_;
goto v___jp_459_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_k_481_);
return v___x_485_;
}
}
else
{
v___y_469_ = v___x_466_;
goto v___jp_468_;
}
}
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_k_455_);
return v___x_488_;
}
v___jp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_463_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_462_, v___y_460_, v___y_461_);
return v___x_463_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_455_ = stack[0].m_obj;
lean_object* v___y_456_ = stack[1].m_obj;
lean_object* v___y_457_ = stack[2].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_455_, v___y_456_, v___y_457_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_494_;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_495_, lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
switch(lean_obj_tag(v_x_496_))
{
case 1:
{
lean_object* v_pre_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_pre_500_ = lean_ctor_get(v_x_496_, 0);
lean_inc(v_pre_500_);
lean_inc(v_k_495_);
v___x_501_ = l_Lean_Name_append(v_x_496_, v_k_495_);
v___x_502_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_501_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_dec(v_pre_500_);
lean_dec(v_k_495_);
return v___x_502_;
}
else
{
lean_object* v_a_503_; uint8_t v___y_505_; uint8_t v___x_507_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v___x_507_ = l_Lean_Exception_isInterrupt(v_a_503_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
lean_inc(v_a_503_);
v___x_508_ = l_Lean_Exception_isRuntime(v_a_503_);
v___y_505_ = v___x_508_;
goto v___jp_504_;
}
else
{
v___y_505_ = v___x_507_;
goto v___jp_504_;
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
lean_dec_ref_known(v___x_502_, 1);
v_x_496_ = v_pre_500_;
goto _start;
}
else
{
lean_dec(v_pre_500_);
lean_dec(v_k_495_);
return v___x_502_;
}
}
}
}
case 0:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_495_, v___y_497_, v___y_498_);
return v___x_509_;
}
default: 
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_x_496_);
lean_dec(v_k_495_);
v___x_510_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_511_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_510_, v___y_497_, v___y_498_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_495_ = stack[0].m_obj;
lean_object* v_x_496_ = stack[1].m_obj;
lean_object* v___y_497_ = stack[2].m_obj;
lean_object* v___y_498_ = stack[3].m_obj;
lean_object* v_res_512_;
v_res_512_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_495_, v_x_496_, v___y_497_, v___y_498_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_513_, lean_object* v_x_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_513_, v_x_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_518_;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_toCold_523_; lean_object* v_currNamespace_524_; lean_object* v___x_525_; 
v_toCold_523_ = lean_ctor_get(v_a_520_, 0);
v_currNamespace_524_ = lean_ctor_get(v_toCold_523_, 4);
lean_inc(v_currNamespace_524_);
v___x_525_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_519_, v_currNamespace_524_, v_a_520_, v_a_521_);
return v___x_525_;
}
}
LEAN_EXPORT void l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_519_ = stack[0].m_obj;
lean_object* v_a_520_ = stack[1].m_obj;
lean_object* v_a_521_ = stack[2].m_obj;
lean_object* v_res_526_;
v_res_526_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_519_, v_a_520_, v_a_521_);
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_531_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_533_ = stack[1].m_obj;
lean_object* v___y_534_ = stack[2].m_obj;
lean_object* v___y_535_ = stack[3].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_box(0), v_msg_533_, v___y_534_, v___y_535_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_539_, v_msg_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_551_, lean_object* v_stx_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Attribute_Builtin_getId(v_stx_552_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___x_567_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc_n(v_a_557_, 2);
lean_dec_ref_known(v___x_556_, 1);
v___x_567_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_557_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_dec(v_a_557_);
lean_dec(v_defaultParserNamespace_551_);
return v___x_567_;
}
else
{
lean_object* v_a_568_; uint8_t v___y_570_; uint8_t v___x_576_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v___x_576_ = l_Lean_Exception_isInterrupt(v_a_568_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; 
lean_inc(v_a_568_);
v___x_577_ = l_Lean_Exception_isRuntime(v_a_568_);
v___y_570_ = v___x_577_;
goto v___jp_569_;
}
else
{
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
v___jp_569_:
{
if (v___y_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref_known(v___x_567_, 1);
lean_inc(v_a_557_);
v___x_571_ = l_Lean_Name_append(v_defaultParserNamespace_551_, v_a_557_);
v___x_572_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_571_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_dec(v_a_557_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; uint8_t v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v___x_574_ = l_Lean_Exception_isInterrupt(v_a_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; 
lean_inc(v_a_573_);
v___x_575_ = l_Lean_Exception_isRuntime(v_a_573_);
v___y_559_ = v___x_572_;
v___y_560_ = v___x_575_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_572_;
v___y_560_ = v___x_574_;
goto v___jp_558_;
}
}
}
else
{
lean_dec(v_a_557_);
lean_dec(v_defaultParserNamespace_551_);
return v___x_567_;
}
}
}
v___jp_558_:
{
if (v___y_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v___y_559_);
v___x_561_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_562_ = l_Lean_MessageData_ofName(v_a_557_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_565_, v_a_553_, v_a_554_);
return v___x_566_;
}
else
{
lean_dec(v_a_557_);
return v___y_559_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_551_);
return v___x_556_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_syntaxNodeKindOfAttrParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultParserNamespace_551_ = stack[0].m_obj;
lean_object* v_stx_552_ = stack[1].m_obj;
lean_object* v_a_553_ = stack[2].m_obj;
lean_object* v_a_554_ = stack[3].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_551_, v_stx_552_, v_a_553_, v_a_554_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_579_, lean_object* v_stx_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_579_, v_stx_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_589_, lean_object* v_opts_590_, lean_object* v_constName_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_593_ = l_Lean_Environment_evalConstCheck___redArg(v_env_589_, v_opts_590_, v___x_592_, v_constName_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_594_, lean_object* v_opts_595_, lean_object* v_constName_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_594_, v_opts_595_, v_constName_596_);
lean_dec_ref(v_opts_595_);
return v_res_597_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_623_ = l_Lean_mkAtom(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_625_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_626_ = lean_array_push(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_636_ = l_Lean_mkAtom(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_638_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_639_ = lean_array_push(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_641_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_642_ = lean_box(2);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
lean_ctor_set(v___x_643_, 2, v___x_640_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_645_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_646_ = lean_array_push(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_648_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_649_ = lean_box(2);
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
lean_ctor_set(v___x_650_, 2, v___x_647_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_652_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_653_ = lean_array_push(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_655_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_656_ = lean_box(2);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_659_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_660_ = lean_array_push(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_662_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_663_ = lean_box(2);
v___x_664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
lean_ctor_set(v___x_664_, 2, v___x_661_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_666_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_667_ = lean_array_push(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_669_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_670_ = lean_box(2);
v___x_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
lean_ctor_set(v___x_671_, 2, v___x_668_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_672_;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_673_, lean_object* v_declName_674_, lean_object* v_kind_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
if (v_builtin_673_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_declName_674_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_674_, v___y_676_, v___y_677_);
return v___x_681_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_mkElabAttribute___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_builtin_673_ = stack[0].m_num;
lean_object* v_declName_674_ = stack[1].m_obj;
lean_object* v_kind_675_ = stack[2].m_obj;
lean_object* v___y_676_ = stack[3].m_obj;
lean_object* v___y_677_ = stack[4].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_673_, v_declName_674_, v_kind_675_, v___y_676_, v___y_677_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_683_, lean_object* v_declName_684_, lean_object* v_kind_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_builtin_boxed_689_; lean_object* v_res_690_; 
v_builtin_boxed_689_ = lean_unbox(v_builtin_683_);
v_res_690_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_689_, v_declName_684_, v_kind_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v_kind_685_);
return v_res_690_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v_infoState_695_; uint8_t v_enabled_696_; 
v___x_694_ = lean_st_ref_get(v___y_692_);
v_infoState_695_ = lean_ctor_get(v___x_694_, 8);
lean_inc_ref(v_infoState_695_);
lean_dec(v___x_694_);
v_enabled_696_ = lean_ctor_get_uint8(v_infoState_695_, sizeof(void*)*3);
lean_dec_ref(v_infoState_695_);
if (v_enabled_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec_ref(v_t_691_);
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v_infoState_700_; lean_object* v_env_701_; lean_object* v_nextMacroScope_702_; lean_object* v_ngen_703_; lean_object* v_auxDeclNGen_704_; lean_object* v_traceState_705_; lean_object* v_cache_706_; lean_object* v_recordedDeps_707_; lean_object* v_messages_708_; lean_object* v_snapshotTasks_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_731_; 
v___x_699_ = lean_st_ref_take(v___y_692_);
v_infoState_700_ = lean_ctor_get(v___x_699_, 8);
v_env_701_ = lean_ctor_get(v___x_699_, 0);
v_nextMacroScope_702_ = lean_ctor_get(v___x_699_, 1);
v_ngen_703_ = lean_ctor_get(v___x_699_, 2);
v_auxDeclNGen_704_ = lean_ctor_get(v___x_699_, 3);
v_traceState_705_ = lean_ctor_get(v___x_699_, 4);
v_cache_706_ = lean_ctor_get(v___x_699_, 5);
v_recordedDeps_707_ = lean_ctor_get(v___x_699_, 6);
v_messages_708_ = lean_ctor_get(v___x_699_, 7);
v_snapshotTasks_709_ = lean_ctor_get(v___x_699_, 9);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_731_ == 0)
{
v___x_711_ = v___x_699_;
v_isShared_712_ = v_isSharedCheck_731_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_snapshotTasks_709_);
lean_inc(v_infoState_700_);
lean_inc(v_messages_708_);
lean_inc(v_recordedDeps_707_);
lean_inc(v_cache_706_);
lean_inc(v_traceState_705_);
lean_inc(v_auxDeclNGen_704_);
lean_inc(v_ngen_703_);
lean_inc(v_nextMacroScope_702_);
lean_inc(v_env_701_);
lean_dec(v___x_699_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_731_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v_enabled_713_; lean_object* v_assignment_714_; lean_object* v_lazyAssignment_715_; lean_object* v_trees_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_730_; 
v_enabled_713_ = lean_ctor_get_uint8(v_infoState_700_, sizeof(void*)*3);
v_assignment_714_ = lean_ctor_get(v_infoState_700_, 0);
v_lazyAssignment_715_ = lean_ctor_get(v_infoState_700_, 1);
v_trees_716_ = lean_ctor_get(v_infoState_700_, 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_infoState_700_);
if (v_isSharedCheck_730_ == 0)
{
v___x_718_ = v_infoState_700_;
v_isShared_719_ = v_isSharedCheck_730_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_trees_716_);
lean_inc(v_lazyAssignment_715_);
lean_inc(v_assignment_714_);
lean_dec(v_infoState_700_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_730_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Lean_PersistentArray_push___redArg(v_trees_716_, v_t_691_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_assignment_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_lazyAssignment_715_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v___x_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*3, v_enabled_713_);
v___x_723_ = v_reuseFailAlloc_729_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 8, v___x_723_);
v___x_725_ = v___x_711_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_env_701_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_nextMacroScope_702_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_ngen_703_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_auxDeclNGen_704_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_traceState_705_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_cache_706_);
lean_ctor_set(v_reuseFailAlloc_728_, 6, v_recordedDeps_707_);
lean_ctor_set(v_reuseFailAlloc_728_, 7, v_messages_708_);
lean_ctor_set(v_reuseFailAlloc_728_, 8, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_728_, 9, v_snapshotTasks_709_);
v___x_725_ = v_reuseFailAlloc_728_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_st_ref_put(v___y_692_, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_720_);
return v___x_727_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_691_ = stack[0].m_obj;
lean_object* v___y_692_ = stack[1].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_691_, v___y_692_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_733_, v___y_734_);
lean_dec(v___y_734_);
return v_res_736_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(32u);
v___x_738_ = lean_mk_empty_array_with_capacity(v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = ((size_t)5ULL);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_unsigned_to_nat(32u);
v___x_743_ = lean_mk_empty_array_with_capacity(v___x_742_);
v___x_744_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_745_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_ctor_set(v___x_745_, 2, v___x_741_);
lean_ctor_set(v___x_745_, 3, v___x_741_);
lean_ctor_set_usize(v___x_745_, 4, v___x_740_);
return v___x_745_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; lean_object* v_infoState_751_; uint8_t v_enabled_752_; 
v___x_750_ = lean_st_ref_get(v___y_748_);
v_infoState_751_ = lean_ctor_get(v___x_750_, 8);
lean_inc_ref(v_infoState_751_);
lean_dec(v___x_750_);
v_enabled_752_ = lean_ctor_get_uint8(v_infoState_751_, sizeof(void*)*3);
lean_dec_ref(v_infoState_751_);
if (v_enabled_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_t_746_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v_t_746_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_756_, v___y_748_);
return v___x_757_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_746_ = stack[0].m_obj;
lean_object* v___y_747_ = stack[1].m_obj;
lean_object* v___y_748_ = stack[2].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_746_, v___y_747_, v___y_748_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__14));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__16));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__18));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__20));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_797_, lean_object* v_declHint_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_env_803_; uint8_t v___x_804_; 
v___x_801_ = lean_box(0);
v___x_802_ = lean_st_ref_get(v___y_799_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = l_Lean_Name_isAnonymous(v_declHint_798_);
if (v___x_804_ == 0)
{
uint8_t v_isExporting_805_; 
v_isExporting_805_ = lean_ctor_get_uint8(v_env_803_, sizeof(void*)*13);
if (v_isExporting_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_msg_797_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
lean_inc_ref(v_env_803_);
v___x_807_ = l_Lean_Environment_setExporting(v_env_803_, v___x_804_);
lean_inc(v_declHint_798_);
lean_inc_ref(v___x_807_);
v___x_808_ = l_Lean_Environment_contains(v___x_807_, v_declHint_798_, v_isExporting_805_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v___x_807_);
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_msg_797_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_c_815_; lean_object* v___x_816_; 
v___x_810_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_811_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_812_ = l_Lean_Options_empty;
v___x_813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_813_, 0, v___x_807_);
lean_ctor_set(v___x_813_, 1, v___x_810_);
lean_ctor_set(v___x_813_, 2, v___x_811_);
lean_ctor_set(v___x_813_, 3, v___x_812_);
lean_inc(v_declHint_798_);
v___x_814_ = l_Lean_MessageData_ofConstName(v_declHint_798_, v___x_804_);
v_c_815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_815_, 0, v___x_813_);
lean_ctor_set(v_c_815_, 1, v___x_814_);
v___x_816_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_803_, v_declHint_798_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_c_815_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_MessageData_note(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v_msg_797_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_880_; 
v_val_824_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_880_ == 0)
{
v___x_826_ = v___x_816_;
v_isShared_827_ = v_isSharedCheck_880_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_816_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_880_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v_modules_829_; lean_object* v_moduleNames_830_; lean_object* v_mod_831_; uint8_t v___y_833_; uint8_t v___x_863_; 
v___x_828_ = l_Lean_Environment_header(v_env_803_);
lean_dec_ref(v_env_803_);
v_modules_829_ = lean_ctor_get(v___x_828_, 3);
lean_inc_ref(v_modules_829_);
v_moduleNames_830_ = lean_ctor_get(v___x_828_, 4);
lean_inc_ref(v_moduleNames_830_);
lean_dec_ref(v___x_828_);
v_mod_831_ = lean_array_get(v___x_801_, v_moduleNames_830_, v_val_824_);
lean_dec_ref(v_moduleNames_830_);
v___x_863_ = l_Lean_isPrivateName(v_declHint_798_);
lean_dec(v_declHint_798_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_array_get_size(v_modules_829_);
v___x_865_ = lean_nat_dec_lt(v_val_824_, v___x_864_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_modules_829_);
lean_dec(v_val_824_);
v___y_833_ = v___x_863_;
goto v___jp_832_;
}
else
{
lean_object* v___x_866_; lean_object* v_toImport_867_; uint8_t v_isExported_868_; 
v___x_866_ = lean_array_fget(v_modules_829_, v_val_824_);
lean_dec(v_val_824_);
lean_dec_ref(v_modules_829_);
v_toImport_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc_ref(v_toImport_867_);
lean_dec(v___x_866_);
v_isExported_868_ = lean_ctor_get_uint8(v_toImport_867_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_867_);
v___y_833_ = v_isExported_868_;
goto v___jp_832_;
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec_ref(v_modules_829_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
v___x_869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_c_815_);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__19);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_MessageData_ofName(v_mod_831_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__21);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_MessageData_note(v___x_876_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v_msg_797_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
v___jp_832_:
{
if (v___y_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_c_815_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_MessageData_ofName(v_mod_831_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_MessageData_note(v___x_841_);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v_msg_797_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_843_);
v___x_845_ = v___x_826_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_c_815_);
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_MessageData_ofName(v_mod_831_);
lean_inc_ref(v___x_851_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__15);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v___x_851_);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__17);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_note(v___x_857_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v_msg_797_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_859_);
v___x_861_ = v___x_826_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
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
lean_object* v___x_881_; 
lean_dec_ref(v_env_803_);
lean_dec(v_declHint_798_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_msg_797_);
return v___x_881_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_797_ = stack[0].m_obj;
lean_object* v_declHint_798_ = stack[1].m_obj;
lean_object* v___y_799_ = stack[2].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_797_, v_declHint_798_, v___y_799_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_883_, lean_object* v_declHint_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_883_, v_declHint_884_, v___y_885_);
lean_dec(v___y_885_);
return v_res_887_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_888_, lean_object* v_declHint_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_903_; 
v___x_893_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_888_, v_declHint_889_, v___y_891_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_898_ = l_Lean_unknownIdentifierMessageTag;
v___x_899_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_888_ = stack[0].m_obj;
lean_object* v_declHint_889_ = stack[1].m_obj;
lean_object* v___y_890_ = stack[2].m_obj;
lean_object* v___y_891_ = stack[3].m_obj;
lean_object* v_res_904_;
v_res_904_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_888_, v_declHint_889_, v___y_890_, v___y_891_);
stack->m_obj
 = v_res_904_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_905_, lean_object* v_declHint_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_905_, v_declHint_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_910_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_911_, lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_toCold_916_; lean_object* v_currRecDepth_917_; lean_object* v_ref_918_; uint16_t v_optionFlags_919_; uint8_t v_suppressElabErrors_920_; uint8_t v_isRecordingDeps_921_; lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_toCold_916_ = lean_ctor_get(v___y_913_, 0);
v_currRecDepth_917_ = lean_ctor_get(v___y_913_, 1);
v_ref_918_ = lean_ctor_get(v___y_913_, 2);
v_optionFlags_919_ = lean_ctor_get_uint16(v___y_913_, sizeof(void*)*3);
v_suppressElabErrors_920_ = lean_ctor_get_uint8(v___y_913_, sizeof(void*)*3 + 2);
v_isRecordingDeps_921_ = lean_ctor_get_uint8(v___y_913_, sizeof(void*)*3 + 3);
v_ref_922_ = l_Lean_replaceRef(v_ref_911_, v_ref_918_);
lean_inc(v_currRecDepth_917_);
lean_inc_ref(v_toCold_916_);
v___x_923_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_923_, 0, v_toCold_916_);
lean_ctor_set(v___x_923_, 1, v_currRecDepth_917_);
lean_ctor_set(v___x_923_, 2, v_ref_922_);
lean_ctor_set_uint16(v___x_923_, sizeof(void*)*3, v_optionFlags_919_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*3 + 2, v_suppressElabErrors_920_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*3 + 3, v_isRecordingDeps_921_);
v___x_924_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_912_, v___x_923_, v___y_914_);
lean_dec_ref_known(v___x_923_, 3);
return v___x_924_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_911_ = stack[0].m_obj;
lean_object* v_msg_912_ = stack[1].m_obj;
lean_object* v___y_913_ = stack[2].m_obj;
lean_object* v___y_914_ = stack[3].m_obj;
lean_object* v_res_925_;
v_res_925_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_911_, v_msg_912_, v___y_913_, v___y_914_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_926_, lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_926_, v_msg_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_ref_926_);
return v_res_931_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_932_, lean_object* v_msg_933_, lean_object* v_declHint_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_940_; 
v___x_938_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_933_, v_declHint_934_, v___y_935_, v___y_936_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_938_);
v___x_940_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_932_, v_a_939_, v___y_935_, v___y_936_);
return v___x_940_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_932_ = stack[0].m_obj;
lean_object* v_msg_933_ = stack[1].m_obj;
lean_object* v_declHint_934_ = stack[2].m_obj;
lean_object* v___y_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_932_, v_msg_933_, v_declHint_934_, v___y_935_, v___y_936_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_942_, lean_object* v_msg_943_, lean_object* v_declHint_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_942_, v_msg_943_, v_declHint_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v_ref_942_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_952_, lean_object* v_constName_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_957_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_958_ = 0;
lean_inc(v_constName_953_);
v___x_959_ = l_Lean_MessageData_ofConstName(v_constName_953_, v___x_958_);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_957_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_952_, v___x_962_, v_constName_953_, v___y_954_, v___y_955_);
return v___x_963_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_952_ = stack[0].m_obj;
lean_object* v_constName_953_ = stack[1].m_obj;
lean_object* v___y_954_ = stack[2].m_obj;
lean_object* v___y_955_ = stack[3].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_952_, v_constName_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_965_, lean_object* v_constName_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_965_, v_constName_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_ref_965_);
return v_res_970_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_ref_975_; lean_object* v___x_976_; 
v_ref_975_ = lean_ctor_get(v___y_972_, 2);
v___x_976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_975_, v_constName_971_, v___y_972_, v___y_973_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_971_ = stack[0].m_obj;
lean_object* v___y_972_ = stack[1].m_obj;
lean_object* v___y_973_ = stack[2].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_971_, v___y_972_, v___y_973_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_982_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_env_988_; uint8_t v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v___x_989_ = 0;
lean_inc(v_constName_983_);
v___x_990_ = l_Lean_Environment_findConstVal_x3f(v_env_988_, v_constName_983_, v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_983_, v___y_984_, v___y_985_);
return v___x_991_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_constName_983_);
v_val_992_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_990_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_dec(v___x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 0);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_983_ = stack[0].m_obj;
lean_object* v___y_984_ = stack[1].m_obj;
lean_object* v___y_985_ = stack[2].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_983_, v___y_984_, v___y_985_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
if (lean_obj_tag(v_a_1006_) == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = l_List_reverse___redArg(v_a_1007_);
return v___x_1008_;
}
else
{
lean_object* v_head_1009_; lean_object* v_tail_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
v_head_1009_ = lean_ctor_get(v_a_1006_, 0);
v_tail_1010_ = lean_ctor_get(v_a_1006_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v_a_1006_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_tail_1010_);
lean_inc(v_head_1009_);
lean_dec(v_a_1006_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = l_Lean_mkLevelParam(v_head_1009_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v_a_1007_);
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_a_1007_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v_a_1006_ = v_tail_1010_;
v_a_1007_ = v___x_1016_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
lean_inc(v_constName_1020_);
v___x_1024_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1036_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1036_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_levelParams_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_levelParams_1029_ = lean_ctor_get(v_a_1025_, 1);
lean_inc(v_levelParams_1029_);
lean_dec(v_a_1025_);
v___x_1030_ = lean_box(0);
v___x_1031_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_1029_, v___x_1030_);
v___x_1032_ = l_Lean_mkConst(v_constName_1020_, v___x_1031_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1032_);
v___x_1034_ = v___x_1027_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_constName_1020_);
v_a_1037_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1024_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1024_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1020_ = stack[0].m_obj;
lean_object* v___y_1021_ = stack[1].m_obj;
lean_object* v___y_1022_ = stack[2].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_1020_, v___y_1021_, v___y_1022_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1050_;
}
}
lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_1051_, lean_object* v_n_1052_, lean_object* v_expectedType_x3f_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_1052_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_stx_1051_);
v___x_1061_ = l_Lean_LocalContext_empty;
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v_expectedType_x3f_1053_);
lean_ctor_set(v___x_1063_, 3, v_a_1058_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*4, v___x_1062_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*4 + 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1064_, v___y_1054_, v___y_1055_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_expectedType_x3f_1053_);
lean_dec(v_stx_1051_);
v_a_1066_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1057_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1057_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1051_ = stack[0].m_obj;
lean_object* v_n_1052_ = stack[1].m_obj;
lean_object* v_expectedType_x3f_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1051_, v_n_1052_, v_expectedType_x3f_1053_, v___y_1054_, v___y_1055_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1075_, lean_object* v_n_1076_, lean_object* v_expectedType_x3f_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1075_, v_n_1076_, v_expectedType_x3f_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0(lean_object* v___x_1082_, lean_object* v_entry_1083_, lean_object* v_s_1084_){
_start:
{
lean_object* v_addEntryFn_1085_; lean_object* v_importedEntries_1086_; lean_object* v_state_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_addEntryFn_1085_ = lean_ctor_get(v___x_1082_, 3);
lean_inc(v_addEntryFn_1085_);
lean_dec_ref(v___x_1082_);
v_importedEntries_1086_ = lean_ctor_get(v_s_1084_, 0);
v_state_1087_ = lean_ctor_get(v_s_1084_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_s_1084_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1089_ = v_s_1084_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_state_1087_);
lean_inc(v_importedEntries_1086_);
lean_dec(v_s_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_state_1091_; lean_object* v___x_1093_; 
v_state_1091_ = lean_apply_2(v_addEntryFn_1085_, v_state_1087_, v_entry_1083_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_state_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_importedEntries_1086_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_state_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1096_, lean_object* v_i_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_array_get_size(v_keys_1096_);
v___x_1100_ = lean_nat_dec_lt(v_i_1097_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_dec(v_i_1097_);
return v___x_1100_;
}
else
{
lean_object* v_k_x27_1101_; uint8_t v___x_1102_; 
v_k_x27_1101_ = lean_array_fget_borrowed(v_keys_1096_, v_i_1097_);
v___x_1102_ = l_Lean_instBEqExtraModUse_beq(v_k_1098_, v_k_x27_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_i_1097_, v___x_1103_);
lean_dec(v_i_1097_);
v_i_1097_ = v___x_1104_;
goto _start;
}
else
{
lean_dec(v_i_1097_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1096_ = stack[0].m_obj;
lean_object* v_i_1097_ = stack[1].m_obj;
lean_object* v_k_1098_ = stack[2].m_obj;
uint8_t v_res_1106_;
v_res_1106_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1096_, v_i_1097_, v_k_1098_);
stack->m_num = v_res_1106_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1107_, lean_object* v_i_1108_, lean_object* v_k_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1107_, v_i_1108_, v_k_1109_);
lean_dec_ref(v_k_1109_);
lean_dec_ref(v_keys_1107_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1112_, size_t v_x_1113_, lean_object* v_x_1114_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_es_1115_; lean_object* v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v_j_1119_; lean_object* v___x_1120_; 
v_es_1115_ = lean_ctor_get(v_x_1112_, 0);
v___x_1116_ = lean_box(2);
v___x_1117_ = ((size_t)31ULL);
v___x_1118_ = lean_usize_land(v_x_1113_, v___x_1117_);
v_j_1119_ = lean_usize_to_nat(v___x_1118_);
v___x_1120_ = lean_array_get_borrowed(v___x_1116_, v_es_1115_, v_j_1119_);
lean_dec(v_j_1119_);
switch(lean_obj_tag(v___x_1120_))
{
case 0:
{
lean_object* v_key_1121_; uint8_t v___x_1122_; 
v_key_1121_ = lean_ctor_get(v___x_1120_, 0);
v___x_1122_ = l_Lean_instBEqExtraModUse_beq(v_x_1114_, v_key_1121_);
return v___x_1122_;
}
case 1:
{
lean_object* v_node_1123_; size_t v___x_1124_; size_t v___x_1125_; 
v_node_1123_ = lean_ctor_get(v___x_1120_, 0);
v___x_1124_ = ((size_t)5ULL);
v___x_1125_ = lean_usize_shift_right(v_x_1113_, v___x_1124_);
v_x_1112_ = v_node_1123_;
v_x_1113_ = v___x_1125_;
goto _start;
}
default: 
{
uint8_t v___x_1127_; 
v___x_1127_ = 0;
return v___x_1127_;
}
}
}
else
{
lean_object* v_ks_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_ks_1128_ = lean_ctor_get(v_x_1112_, 0);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1128_, v___x_1129_, v_x_1114_);
return v___x_1130_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1112_ = stack[0].m_obj;
size_t v_x_1113_ = stack[1].m_num;
lean_object* v_x_1114_ = stack[2].m_obj;
uint8_t v_res_1131_;
v_res_1131_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1112_, v_x_1113_, v_x_1114_);
stack->m_num = v_res_1131_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
size_t v_x_7076__boxed_1135_; uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_x_7076__boxed_1135_ = lean_unbox_usize(v_x_1133_);
lean_dec(v_x_1133_);
v_res_1136_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1132_, v_x_7076__boxed_1135_, v_x_1134_);
lean_dec_ref(v_x_1134_);
lean_dec_ref(v_x_1132_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint64_t v___x_1140_; size_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = l_Lean_instHashableExtraModUse_hash(v_x_1139_);
v___x_1141_ = lean_uint64_to_usize(v___x_1140_);
v___x_1142_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1138_, v___x_1141_, v_x_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1138_ = stack[0].m_obj;
lean_object* v_x_1139_ = stack[1].m_obj;
uint8_t v_res_1143_;
v_res_1143_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1138_, v_x_1139_);
stack->m_num = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1144_, v_x_1145_);
lean_dec_ref(v_x_1145_);
lean_dec_ref(v_x_1144_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1148_; double v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_float_of_nat(v___x_1148_);
return v___x_1149_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1153_, lean_object* v_msg_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_ref_1158_; lean_object* v___x_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1205_; 
v_ref_1158_ = lean_ctor_get(v___y_1155_, 2);
v___x_1159_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1154_, v___y_1155_, v___y_1156_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1205_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1205_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v_traceState_1165_; lean_object* v_env_1166_; lean_object* v_nextMacroScope_1167_; lean_object* v_ngen_1168_; lean_object* v_auxDeclNGen_1169_; lean_object* v_cache_1170_; lean_object* v_recordedDeps_1171_; lean_object* v_messages_1172_; lean_object* v_infoState_1173_; lean_object* v_snapshotTasks_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1204_; 
v___x_1164_ = lean_st_ref_take(v___y_1156_);
v_traceState_1165_ = lean_ctor_get(v___x_1164_, 4);
v_env_1166_ = lean_ctor_get(v___x_1164_, 0);
v_nextMacroScope_1167_ = lean_ctor_get(v___x_1164_, 1);
v_ngen_1168_ = lean_ctor_get(v___x_1164_, 2);
v_auxDeclNGen_1169_ = lean_ctor_get(v___x_1164_, 3);
v_cache_1170_ = lean_ctor_get(v___x_1164_, 5);
v_recordedDeps_1171_ = lean_ctor_get(v___x_1164_, 6);
v_messages_1172_ = lean_ctor_get(v___x_1164_, 7);
v_infoState_1173_ = lean_ctor_get(v___x_1164_, 8);
v_snapshotTasks_1174_ = lean_ctor_get(v___x_1164_, 9);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1176_ = v___x_1164_;
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snapshotTasks_1174_);
lean_inc(v_infoState_1173_);
lean_inc(v_messages_1172_);
lean_inc(v_recordedDeps_1171_);
lean_inc(v_cache_1170_);
lean_inc(v_traceState_1165_);
lean_inc(v_auxDeclNGen_1169_);
lean_inc(v_ngen_1168_);
lean_inc(v_nextMacroScope_1167_);
lean_inc(v_env_1166_);
lean_dec(v___x_1164_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1204_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
uint64_t v_tid_1178_; lean_object* v_traces_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1203_; 
v_tid_1178_ = lean_ctor_get_uint64(v_traceState_1165_, sizeof(void*)*1);
v_traces_1179_ = lean_ctor_get(v_traceState_1165_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_traceState_1165_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1181_ = v_traceState_1165_;
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_traces_1179_);
lean_dec(v_traceState_1165_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; double v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1186_ = 0;
v___x_1187_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1188_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1188_, 0, v_cls_1153_);
lean_ctor_set(v___x_1188_, 1, v___x_1184_);
lean_ctor_set(v___x_1188_, 2, v___x_1187_);
lean_ctor_set_float(v___x_1188_, sizeof(void*)*3, v___x_1185_);
lean_ctor_set_float(v___x_1188_, sizeof(void*)*3 + 8, v___x_1185_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*3 + 16, v___x_1186_);
v___x_1189_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1190_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v_a_1160_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
lean_inc(v_ref_1158_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_ref_1158_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_PersistentArray_push___redArg(v_traces_1179_, v___x_1191_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1192_);
v___x_1194_ = v___x_1181_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1192_);
lean_ctor_set_uint64(v_reuseFailAlloc_1202_, sizeof(void*)*1, v_tid_1178_);
v___x_1194_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 4, v___x_1194_);
v___x_1196_ = v___x_1176_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_env_1166_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_nextMacroScope_1167_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_ngen_1168_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_auxDeclNGen_1169_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v_cache_1170_);
lean_ctor_set(v_reuseFailAlloc_1201_, 6, v_recordedDeps_1171_);
lean_ctor_set(v_reuseFailAlloc_1201_, 7, v_messages_1172_);
lean_ctor_set(v_reuseFailAlloc_1201_, 8, v_infoState_1173_);
lean_ctor_set(v_reuseFailAlloc_1201_, 9, v_snapshotTasks_1174_);
v___x_1196_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_st_ref_put(v___y_1156_, v___x_1196_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1183_);
v___x_1199_ = v___x_1162_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1183_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1153_ = stack[0].m_obj;
lean_object* v_msg_1154_ = stack[1].m_obj;
lean_object* v___y_1155_ = stack[2].m_obj;
lean_object* v___y_1156_ = stack[3].m_obj;
lean_object* v_res_1206_;
v_res_1206_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1153_, v_msg_1154_, v___y_1155_, v___y_1156_);
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1207_, lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1207_, v_msg_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1212_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v_cls_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_cls_1232_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1233_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1234_ = l_Lean_Name_append(v___x_1233_, v_cls_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
return v___x_1240_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1245_, uint8_t v_isMeta_1246_, lean_object* v_hint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_env_1269_; uint8_t v_isExporting_1270_; lean_object* v_entry_1271_; lean_object* v___x_1272_; lean_object* v_env_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1267_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
v___x_1268_ = lean_st_ref_get(v___y_1249_);
v_env_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc_ref(v_env_1269_);
lean_dec(v___x_1268_);
v_isExporting_1270_ = lean_ctor_get_uint8(v_env_1269_, sizeof(void*)*13);
lean_dec_ref(v_env_1269_);
lean_inc(v_mod_1245_);
v_entry_1271_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1271_, 0, v_mod_1245_);
lean_ctor_set_uint8(v_entry_1271_, sizeof(void*)*1, v_isExporting_1270_);
lean_ctor_set_uint8(v_entry_1271_, sizeof(void*)*1 + 1, v_isMeta_1246_);
v___x_1272_ = lean_st_ref_get(v___y_1249_);
v_env_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_env_1273_);
lean_dec(v___x_1272_);
v___x_1274_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1275_ = lean_box(1);
v___x_1276_ = lean_box(0);
v___x_1277_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1267_, v___x_1274_, v_env_1273_, v___x_1275_, v___x_1276_);
v___x_1278_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1277_, v_entry_1271_);
lean_dec(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v_toCold_1279_; lean_object* v_options_1280_; lean_object* v_inheritedTraceOptions_1281_; uint8_t v_hasTrace_1282_; lean_object* v___f_1283_; uint8_t v___x_1284_; lean_object* v___y_1286_; 
v_toCold_1279_ = lean_ctor_get(v___y_1248_, 0);
v_options_1280_ = lean_ctor_get(v_toCold_1279_, 2);
v_inheritedTraceOptions_1281_ = lean_ctor_get(v_toCold_1279_, 11);
v_hasTrace_1282_ = lean_ctor_get_uint8(v_options_1280_, sizeof(void*)*1);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_1283_, 0, v___x_1274_);
lean_closure_set(v___f_1283_, 1, v_entry_1271_);
v___x_1284_ = 1;
if (v_hasTrace_1282_ == 0)
{
lean_dec(v_hint_1247_);
lean_dec(v_mod_1245_);
v___y_1286_ = v___y_1249_;
goto v___jp_1285_;
}
else
{
lean_object* v_cls_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_cls_1304_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1324_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___x_1325_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1281_, v_options_1280_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_hint_1247_);
lean_dec(v_mod_1245_);
v___y_1286_ = v___y_1249_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1326_; lean_object* v___y_1328_; 
v___x_1326_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1270_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1328_ = v___x_1335_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1328_ = v___x_1336_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_inc_ref(v___y_1328_);
v___x_1329_ = l_Lean_stringToMessageData(v___y_1328_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
if (v_isMeta_1246_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1311_ = v___x_1332_;
v___y_1312_ = v___x_1333_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1334_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1311_ = v___x_1332_;
v___y_1312_ = v___x_1334_;
goto v___jp_1310_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___y_1306_);
lean_ctor_set(v___x_1308_, 1, v___y_1307_);
v___x_1309_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1304_, v___x_1308_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_dec_ref_known(v___x_1309_, 1);
v___y_1286_ = v___y_1249_;
goto v___jp_1285_;
}
else
{
lean_dec_ref(v___f_1283_);
return v___x_1309_;
}
}
v___jp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
lean_inc_ref(v___y_1312_);
v___x_1313_ = l_Lean_stringToMessageData(v___y_1312_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___y_1311_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_MessageData_ofName(v_mod_1245_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_Name_isAnonymous(v_hint_1247_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8);
v___x_1321_ = l_Lean_MessageData_ofName(v_hint_1247_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___y_1306_ = v___x_1318_;
v___y_1307_ = v___x_1322_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_hint_1247_);
v___x_1323_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___y_1306_ = v___x_1318_;
v___y_1307_ = v___x_1323_;
goto v___jp_1305_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v_toEnvExtension_1288_; lean_object* v_env_1289_; lean_object* v_nextMacroScope_1290_; lean_object* v_ngen_1291_; lean_object* v_auxDeclNGen_1292_; lean_object* v_traceState_1293_; lean_object* v_recordedDeps_1294_; lean_object* v_messages_1295_; lean_object* v_infoState_1296_; lean_object* v_snapshotTasks_1297_; lean_object* v_asyncMode_1298_; uint8_t v_logWrites_1299_; lean_object* v___x_1300_; 
v___x_1287_ = lean_st_ref_take(v___y_1286_);
v_toEnvExtension_1288_ = lean_ctor_get(v___x_1274_, 0);
v_env_1289_ = lean_ctor_get(v___x_1287_, 0);
lean_inc_ref(v_env_1289_);
v_nextMacroScope_1290_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_nextMacroScope_1290_);
v_ngen_1291_ = lean_ctor_get(v___x_1287_, 2);
lean_inc_ref(v_ngen_1291_);
v_auxDeclNGen_1292_ = lean_ctor_get(v___x_1287_, 3);
lean_inc_ref(v_auxDeclNGen_1292_);
v_traceState_1293_ = lean_ctor_get(v___x_1287_, 4);
lean_inc_ref(v_traceState_1293_);
v_recordedDeps_1294_ = lean_ctor_get(v___x_1287_, 6);
lean_inc_ref(v_recordedDeps_1294_);
v_messages_1295_ = lean_ctor_get(v___x_1287_, 7);
lean_inc_ref(v_messages_1295_);
v_infoState_1296_ = lean_ctor_get(v___x_1287_, 8);
lean_inc_ref(v_infoState_1296_);
v_snapshotTasks_1297_ = lean_ctor_get(v___x_1287_, 9);
lean_inc_ref(v_snapshotTasks_1297_);
lean_dec(v___x_1287_);
v_asyncMode_1298_ = lean_ctor_get(v_toEnvExtension_1288_, 2);
v_logWrites_1299_ = lean_ctor_get_uint8(v_toEnvExtension_1288_, sizeof(void*)*6);
v___x_1300_ = lean_box(0);
if (v_logWrites_1299_ == 0)
{
lean_object* v___x_1301_; 
lean_inc_ref(v_toEnvExtension_1288_);
v___x_1301_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1288_, v_env_1289_, v___f_1283_, v_asyncMode_1298_, v___x_1276_, v___x_1284_);
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___x_1300_;
v___y_1254_ = v_nextMacroScope_1290_;
v___y_1255_ = v_snapshotTasks_1297_;
v___y_1256_ = v_messages_1295_;
v___y_1257_ = v_recordedDeps_1294_;
v___y_1258_ = v_auxDeclNGen_1292_;
v___y_1259_ = v_traceState_1293_;
v___y_1260_ = v_infoState_1296_;
v___y_1261_ = v_ngen_1291_;
v___y_1262_ = v___x_1301_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc_ref_n(v_toEnvExtension_1288_, 2);
v___x_1302_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1288_, v_env_1289_);
lean_dec_ref(v_env_1289_);
v___x_1303_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1288_, v___x_1302_, v___f_1283_, v_asyncMode_1298_, v___x_1276_, v___x_1284_);
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___x_1300_;
v___y_1254_ = v_nextMacroScope_1290_;
v___y_1255_ = v_snapshotTasks_1297_;
v___y_1256_ = v_messages_1295_;
v___y_1257_ = v_recordedDeps_1294_;
v___y_1258_ = v_auxDeclNGen_1292_;
v___y_1259_ = v_traceState_1293_;
v___y_1260_ = v_infoState_1296_;
v___y_1261_ = v_ngen_1291_;
v___y_1262_ = v___x_1303_;
goto v___jp_1251_;
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref_known(v_entry_1271_, 1);
lean_dec(v_hint_1247_);
lean_dec(v_mod_1245_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
v___jp_1251_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1);
v___x_1264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1264_, 0, v___y_1262_);
lean_ctor_set(v___x_1264_, 1, v___y_1254_);
lean_ctor_set(v___x_1264_, 2, v___y_1261_);
lean_ctor_set(v___x_1264_, 3, v___y_1258_);
lean_ctor_set(v___x_1264_, 4, v___y_1259_);
lean_ctor_set(v___x_1264_, 5, v___x_1263_);
lean_ctor_set(v___x_1264_, 6, v___y_1257_);
lean_ctor_set(v___x_1264_, 7, v___y_1256_);
lean_ctor_set(v___x_1264_, 8, v___y_1260_);
lean_ctor_set(v___x_1264_, 9, v___y_1255_);
v___x_1265_ = lean_st_ref_put(v___y_1252_, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1253_);
return v___x_1266_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1245_ = stack[0].m_obj;
uint8_t v_isMeta_1246_ = stack[1].m_num;
lean_object* v_hint_1247_ = stack[2].m_obj;
lean_object* v___y_1248_ = stack[3].m_obj;
lean_object* v___y_1249_ = stack[4].m_obj;
lean_object* v_res_1339_;
v_res_1339_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1245_, v_isMeta_1246_, v_hint_1247_, v___y_1248_, v___y_1249_);
stack->m_obj
 = v_res_1339_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1340_, lean_object* v_isMeta_1341_, lean_object* v_hint_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_isMeta_boxed_1346_; lean_object* v_res_1347_; 
v_isMeta_boxed_1346_ = lean_unbox(v_isMeta_1341_);
v_res_1347_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1340_, v_isMeta_boxed_1346_, v_hint_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1347_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1348_, lean_object* v_declName_1349_, lean_object* v_as_1350_, size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_declName_1349_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1353_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v_modules_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v_toImport_1364_; lean_object* v_module_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1359_ = l_Lean_Environment_header(v___x_1348_);
v_modules_1360_ = lean_ctor_get(v___x_1359_, 3);
lean_inc_ref(v_modules_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1362_ = lean_array_uget_borrowed(v_as_1350_, v_i_1352_);
v___x_1363_ = lean_array_get(v___x_1361_, v_modules_1360_, v_a_1362_);
lean_dec_ref(v_modules_1360_);
v_toImport_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref(v_toImport_1364_);
lean_dec(v___x_1363_);
v_module_1365_ = lean_ctor_get(v_toImport_1364_, 0);
lean_inc(v_module_1365_);
lean_dec_ref(v_toImport_1364_);
v___x_1366_ = lean_box(0);
v___x_1367_ = 0;
lean_inc(v_declName_1349_);
v___x_1368_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1365_, v___x_1367_, v_declName_1349_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1368_) == 0)
{
size_t v___x_1369_; size_t v___x_1370_; 
lean_dec_ref_known(v___x_1368_, 1);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1352_, v___x_1369_);
v_i_1352_ = v___x_1370_;
v_b_1353_ = v___x_1366_;
goto _start;
}
else
{
lean_dec(v_declName_1349_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1348_ = stack[0].m_obj;
lean_object* v_declName_1349_ = stack[1].m_obj;
lean_object* v_as_1350_ = stack[2].m_obj;
size_t v_sz_1351_ = stack[3].m_num;
size_t v_i_1352_ = stack[4].m_num;
lean_object* v_b_1353_ = stack[5].m_obj;
lean_object* v___y_1354_ = stack[6].m_obj;
lean_object* v___y_1355_ = stack[7].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1348_, v_declName_1349_, v_as_1350_, v_sz_1351_, v_i_1352_, v_b_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1372_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1373_, lean_object* v_declName_1374_, lean_object* v_as_1375_, lean_object* v_sz_1376_, lean_object* v_i_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1373_, v_declName_1374_, v_as_1375_, v_sz_boxed_1382_, v_i_boxed_1383_, v_b_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_as_1375_);
lean_dec_ref(v___x_1373_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_box(0);
return v___x_1387_;
}
else
{
lean_object* v_key_1388_; lean_object* v_value_1389_; lean_object* v_tail_1390_; uint8_t v___x_1391_; 
v_key_1388_ = lean_ctor_get(v_x_1386_, 0);
v_value_1389_ = lean_ctor_get(v_x_1386_, 1);
v_tail_1390_ = lean_ctor_get(v_x_1386_, 2);
v___x_1391_ = lean_name_eq(v_key_1388_, v_a_1385_);
if (v___x_1391_ == 0)
{
v_x_1386_ = v_tail_1390_;
goto _start;
}
else
{
lean_object* v___x_1393_; 
lean_inc(v_value_1389_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_value_1389_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1394_, v_x_1395_);
lean_dec(v_x_1395_);
lean_dec(v_a_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_buckets_1399_; lean_object* v___x_1400_; uint64_t v___y_1402_; 
v_buckets_1399_ = lean_ctor_get(v_m_1397_, 1);
v___x_1400_ = lean_array_get_size(v_buckets_1399_);
if (lean_obj_tag(v_a_1398_) == 0)
{
uint64_t v___x_1416_; 
v___x_1416_ = 1723ULL;
v___y_1402_ = v___x_1416_;
goto v___jp_1401_;
}
else
{
uint64_t v_hash_1417_; 
v_hash_1417_ = lean_ctor_get_uint64(v_a_1398_, sizeof(void*)*2);
v___y_1402_ = v_hash_1417_;
goto v___jp_1401_;
}
v___jp_1401_:
{
uint64_t v___x_1403_; uint64_t v___x_1404_; uint64_t v_fold_1405_; uint64_t v___x_1406_; uint64_t v___x_1407_; uint64_t v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1403_ = 32ULL;
v___x_1404_ = lean_uint64_shift_right(v___y_1402_, v___x_1403_);
v_fold_1405_ = lean_uint64_xor(v___y_1402_, v___x_1404_);
v___x_1406_ = 16ULL;
v___x_1407_ = lean_uint64_shift_right(v_fold_1405_, v___x_1406_);
v___x_1408_ = lean_uint64_xor(v_fold_1405_, v___x_1407_);
v___x_1409_ = lean_uint64_to_usize(v___x_1408_);
v___x_1410_ = lean_usize_of_nat(v___x_1400_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_sub(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_usize_land(v___x_1409_, v___x_1412_);
v___x_1414_ = lean_array_uget_borrowed(v_buckets_1399_, v___x_1413_);
v___x_1415_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1398_, v___x_1414_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_m_1418_);
return v_res_1420_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1421_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1424_, uint8_t v_isMeta_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_env_1434_; lean_object* v___y_1436_; lean_object* v___x_1449_; 
v___x_1429_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0);
v___x_1430_ = lean_st_ref_get(v___y_1427_);
v_env_1434_ = lean_ctor_get(v___x_1430_, 0);
lean_inc_ref(v_env_1434_);
lean_dec(v___x_1430_);
v___x_1449_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1434_, v_declName_1424_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_dec_ref(v_env_1434_);
lean_dec(v_declName_1424_);
goto v___jp_1431_;
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1451_; lean_object* v_modules_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_val_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l_Lean_Environment_header(v_env_1434_);
v_modules_1452_ = lean_ctor_get(v___x_1451_, 3);
lean_inc_ref(v_modules_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = lean_array_get_size(v_modules_1452_);
v___x_1454_ = lean_nat_dec_lt(v_val_1450_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v_modules_1452_);
lean_dec(v_val_1450_);
lean_dec_ref(v_env_1434_);
lean_dec(v_declName_1424_);
goto v___jp_1431_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___y_1458_; 
v___x_1455_ = lean_array_fget(v_modules_1452_, v_val_1450_);
lean_dec(v_val_1450_);
lean_dec_ref(v_modules_1452_);
v___x_1456_ = lean_st_ref_get(v___y_1427_);
if (v_isMeta_1425_ == 0)
{
lean_dec(v___x_1456_);
v___y_1458_ = v_isMeta_1425_;
goto v___jp_1457_;
}
else
{
lean_object* v_env_1469_; uint8_t v___x_1470_; 
v_env_1469_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1469_);
lean_dec(v___x_1456_);
lean_inc(v_declName_1424_);
v___x_1470_ = l_Lean_isMarkedMeta(v_env_1469_, v_declName_1424_);
if (v___x_1470_ == 0)
{
v___y_1458_ = v_isMeta_1425_;
goto v___jp_1457_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = 0;
v___y_1458_ = v___x_1471_;
goto v___jp_1457_;
}
}
v___jp_1457_:
{
lean_object* v_toImport_1459_; lean_object* v_module_1460_; lean_object* v___x_1461_; 
v_toImport_1459_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_ref(v_toImport_1459_);
lean_dec(v___x_1455_);
v_module_1460_ = lean_ctor_get(v_toImport_1459_, 0);
lean_inc(v_module_1460_);
lean_dec_ref(v_toImport_1459_);
lean_inc(v_declName_1424_);
v___x_1461_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1460_, v___y_1458_, v_declName_1424_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1461_, 1);
v___x_1462_ = l_Lean_indirectModUseExt;
v___x_1463_ = lean_box(1);
v___x_1464_ = lean_box(0);
lean_inc_ref(v_env_1434_);
v___x_1465_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1429_, v___x_1462_, v_env_1434_, v___x_1463_, v___x_1464_);
v___x_1466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1465_, v_declName_1424_);
lean_dec(v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___y_1436_ = v___x_1467_;
goto v___jp_1435_;
}
else
{
lean_object* v_val_1468_; 
v_val_1468_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v___x_1466_, 1);
v___y_1436_ = v_val_1468_;
goto v___jp_1435_;
}
}
else
{
lean_dec_ref(v_env_1434_);
lean_dec(v_declName_1424_);
return v___x_1461_;
}
}
}
}
v___jp_1431_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
v___jp_1435_:
{
lean_object* v___x_1437_; size_t v_sz_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_box(0);
v_sz_1438_ = lean_array_size(v___y_1436_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1434_, v_declName_1424_, v___y_1436_, v_sz_1438_, v___x_1439_, v___x_1437_, v___y_1426_, v___y_1427_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_env_1434_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v___x_1440_, 0);
lean_dec(v_unused_1448_);
v___x_1442_ = v___x_1440_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v___x_1440_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1437_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1437_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1424_ = stack[0].m_obj;
uint8_t v_isMeta_1425_ = stack[1].m_num;
lean_object* v___y_1426_ = stack[2].m_obj;
lean_object* v___y_1427_ = stack[3].m_obj;
lean_object* v_res_1472_;
v_res_1472_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1424_, v_isMeta_1425_, v___y_1426_, v___y_1427_);
stack->m_obj
 = v_res_1472_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1473_, lean_object* v_isMeta_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v_isMeta_boxed_1478_; lean_object* v_res_1479_; 
v_isMeta_boxed_1478_ = lean_unbox(v_isMeta_1474_);
v_res_1479_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1473_, v_isMeta_boxed_1478_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1479_;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1480_, uint8_t v_x_1481_, lean_object* v_stx_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
lean_inc(v_stx_1482_);
v___x_1486_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1480_, v_stx_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1539_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1539_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1539_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_env_1492_; uint8_t v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = lean_st_ref_get(v___y_1484_);
v_env_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc_ref(v_env_1492_);
lean_dec(v___x_1491_);
v___x_1493_ = 1;
lean_inc(v_a_1487_);
v___x_1494_ = l_Lean_Environment_contains(v_env_1492_, v_a_1487_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1496_; 
lean_dec(v_stx_1482_);
if (v_isShared_1490_ == 0)
{
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1487_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
uint8_t v___x_1498_; lean_object* v___x_1499_; 
lean_del_object(v___x_1489_);
v___x_1498_ = 0;
lean_inc(v_a_1487_);
v___x_1499_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1487_, v___x_1498_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1499_, 0);
lean_dec(v_unused_1530_);
v___x_1501_ = v___x_1499_;
v_isShared_1502_ = v_isSharedCheck_1529_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v___x_1499_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1529_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v_infoState_1504_; uint8_t v_enabled_1505_; 
v___x_1503_ = lean_st_ref_get(v___y_1484_);
v_infoState_1504_ = lean_ctor_get(v___x_1503_, 8);
lean_inc_ref(v_infoState_1504_);
lean_dec(v___x_1503_);
v_enabled_1505_ = lean_ctor_get_uint8(v_infoState_1504_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1504_);
if (v_enabled_1505_ == 0)
{
lean_object* v___x_1507_; 
lean_dec(v_stx_1482_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_a_1487_);
v___x_1507_ = v___x_1501_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1487_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_del_object(v___x_1501_);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1509_);
lean_dec(v_stx_1482_);
v___x_1511_ = lean_box(0);
lean_inc(v_a_1487_);
v___x_1512_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1510_, v_a_1487_, v___x_1511_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1512_, 0);
lean_dec(v_unused_1520_);
v___x_1514_ = v___x_1512_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v___x_1512_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v_a_1487_);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1487_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_a_1487_);
v_a_1521_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1512_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1512_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1487_);
lean_dec(v_stx_1482_);
v_a_1531_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1499_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1499_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1482_);
return v___x_1486_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_mkElabAttribute___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_parserNamespace_1480_ = stack[0].m_obj;
uint8_t v_x_1481_ = stack[1].m_num;
lean_object* v_stx_1482_ = stack[2].m_obj;
lean_object* v___y_1483_ = stack[3].m_obj;
lean_object* v___y_1484_ = stack[4].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1480_, v_x_1481_, v_stx_1482_, v___y_1483_, v___y_1484_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1541_, lean_object* v_x_1542_, lean_object* v_stx_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_x_7925__boxed_1547_; lean_object* v_res_1548_; 
v_x_7925__boxed_1547_ = lean_unbox(v_x_1542_);
v_res_1548_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1541_, v_x_7925__boxed_1547_, v_stx_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1548_;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1551_, lean_object* v_attrName_1552_, lean_object* v_parserNamespace_1553_, lean_object* v_typeName_1554_, lean_object* v_kind_1555_, lean_object* v_attrDeclName_1556_){
_start:
{
lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___f_1558_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1559_, 0, v_parserNamespace_1553_);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1561_ = lean_string_append(v_kind_1555_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1562_, 0, v_attrBuiltinName_1551_);
lean_ctor_set(v___x_1562_, 1, v_attrName_1552_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
lean_ctor_set(v___x_1562_, 3, v_typeName_1554_);
lean_ctor_set(v___x_1562_, 4, v___f_1559_);
lean_ctor_set(v___x_1562_, 5, v___f_1558_);
v___x_1563_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1562_, v_attrDeclName_1556_);
return v___x_1563_;
}
}
LEAN_EXPORT void l_Lean_Elab_mkElabAttribute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrBuiltinName_1551_ = stack[0].m_obj;
lean_object* v_attrName_1552_ = stack[1].m_obj;
lean_object* v_parserNamespace_1553_ = stack[2].m_obj;
lean_object* v_typeName_1554_ = stack[3].m_obj;
lean_object* v_kind_1555_ = stack[4].m_obj;
lean_object* v_attrDeclName_1556_ = stack[5].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1551_, v_attrName_1552_, v_parserNamespace_1553_, v_typeName_1554_, v_kind_1555_, v_attrDeclName_1556_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1565_, lean_object* v_attrName_1566_, lean_object* v_parserNamespace_1567_, lean_object* v_typeName_1568_, lean_object* v_kind_1569_, lean_object* v_attrDeclName_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1565_, v_attrName_1566_, v_parserNamespace_1567_, v_typeName_1568_, v_kind_1569_, v_attrDeclName_1570_);
return v_res_1572_;
}
}
lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1573_, lean_object* v_attrBuiltinName_1574_, lean_object* v_attrName_1575_, lean_object* v_parserNamespace_1576_, lean_object* v_typeName_1577_, lean_object* v_kind_1578_, lean_object* v_attrDeclName_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1574_, v_attrName_1575_, v_parserNamespace_1576_, v_typeName_1577_, v_kind_1578_, v_attrDeclName_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT void l_Lean_Elab_mkElabAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrBuiltinName_1574_ = stack[1].m_obj;
lean_object* v_attrName_1575_ = stack[2].m_obj;
lean_object* v_parserNamespace_1576_ = stack[3].m_obj;
lean_object* v_typeName_1577_ = stack[4].m_obj;
lean_object* v_kind_1578_ = stack[5].m_obj;
lean_object* v_attrDeclName_1579_ = stack[6].m_obj;
lean_object* v_res_1582_;
v_res_1582_ = l_Lean_Elab_mkElabAttribute(lean_box(0), v_attrBuiltinName_1574_, v_attrName_1575_, v_parserNamespace_1576_, v_typeName_1577_, v_kind_1578_, v_attrDeclName_1579_);
stack->m_obj
 = v_res_1582_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1583_, lean_object* v_attrBuiltinName_1584_, lean_object* v_attrName_1585_, lean_object* v_parserNamespace_1586_, lean_object* v_typeName_1587_, lean_object* v_kind_1588_, lean_object* v_attrDeclName_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1583_, v_attrBuiltinName_1584_, v_attrName_1585_, v_parserNamespace_1586_, v_typeName_1587_, v_kind_1588_, v_attrDeclName_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1592_, lean_object* v_m_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1593_, v_a_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_m_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1596_, v_m_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_m_1597_);
return v_res_1599_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1600_, v___y_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1600_ = stack[0].m_obj;
lean_object* v___y_1601_ = stack[1].m_obj;
lean_object* v___y_1602_ = stack[2].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1600_, v___y_1601_, v___y_1602_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1610_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1612_, v_x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1612_ = stack[1].m_obj;
lean_object* v_x_1613_ = stack[2].m_obj;
uint8_t v_res_1615_;
v_res_1615_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_box(0), v_x_1612_, v_x_1613_);
stack->m_num = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1616_, v_x_1617_, v_x_1618_);
lean_dec_ref(v_x_1618_);
lean_dec_ref(v_x_1617_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1621_, lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1625_, v_a_1626_, v_x_1627_);
lean_dec(v_x_1627_);
lean_dec(v_a_1626_);
return v_res_1628_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, size_t v_x_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1630_, v_x_1631_, v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1630_ = stack[1].m_obj;
size_t v_x_1631_ = stack[2].m_num;
lean_object* v_x_1632_ = stack[3].m_obj;
uint8_t v_res_1634_;
v_res_1634_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_x_1630_, v_x_1631_, v_x_1632_);
stack->m_num = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
size_t v_x_8183__boxed_1639_; uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_x_8183__boxed_1639_ = lean_unbox_usize(v_x_1637_);
lean_dec(v_x_1637_);
v_res_1640_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1635_, v_x_1636_, v_x_8183__boxed_1639_, v_x_1638_);
lean_dec_ref(v_x_1638_);
lean_dec_ref(v_x_1636_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1642_, lean_object* v_constName_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1643_, v___y_1644_, v___y_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1643_ = stack[1].m_obj;
lean_object* v___y_1644_ = stack[2].m_obj;
lean_object* v___y_1645_ = stack[3].m_obj;
lean_object* v_res_1648_;
v_res_1648_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_box(0), v_constName_1643_, v___y_1644_, v___y_1645_);
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1649_, lean_object* v_constName_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1649_, v_constName_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1654_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_k_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1656_, v_i_1659_, v_k_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1656_ = stack[1].m_obj;
lean_object* v_vals_1657_ = stack[2].m_obj;
lean_object* v_i_1659_ = stack[4].m_obj;
lean_object* v_k_1660_ = stack[5].m_obj;
uint8_t v_res_1662_;
v_res_1662_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_box(0), v_keys_1656_, v_vals_1657_, lean_box(0), v_i_1659_, v_k_1660_);
stack->m_num = v_res_1662_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_heq_1666_, lean_object* v_i_1667_, lean_object* v_k_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1663_, v_keys_1664_, v_vals_1665_, v_heq_1666_, v_i_1667_, v_k_1668_);
lean_dec_ref(v_k_1668_);
lean_dec_ref(v_vals_1665_);
lean_dec_ref(v_keys_1664_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1671_, lean_object* v_ref_1672_, lean_object* v_constName_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1672_, v_constName_1673_, v___y_1674_, v___y_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1672_ = stack[1].m_obj;
lean_object* v_constName_1673_ = stack[2].m_obj;
lean_object* v___y_1674_ = stack[3].m_obj;
lean_object* v___y_1675_ = stack[4].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_box(0), v_ref_1672_, v_constName_1673_, v___y_1674_, v___y_1675_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_ref_1680_, lean_object* v_constName_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1679_, v_ref_1680_, v_constName_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v_ref_1680_);
return v_res_1685_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1686_, lean_object* v_ref_1687_, lean_object* v_msg_1688_, lean_object* v_declHint_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1687_, v_msg_1688_, v_declHint_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1687_ = stack[1].m_obj;
lean_object* v_msg_1688_ = stack[2].m_obj;
lean_object* v_declHint_1689_ = stack[3].m_obj;
lean_object* v___y_1690_ = stack[4].m_obj;
lean_object* v___y_1691_ = stack[5].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_box(0), v_ref_1687_, v_msg_1688_, v_declHint_1689_, v___y_1690_, v___y_1691_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_ref_1696_, lean_object* v_msg_1697_, lean_object* v_declHint_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1695_, v_ref_1696_, v_msg_1697_, v_declHint_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_ref_1696_);
return v_res_1702_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1703_, v_declHint_1704_, v___y_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1703_ = stack[0].m_obj;
lean_object* v_declHint_1704_ = stack[1].m_obj;
lean_object* v___y_1705_ = stack[2].m_obj;
lean_object* v___y_1706_ = stack[3].m_obj;
lean_object* v_res_1709_;
v_res_1709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1703_, v_declHint_1704_, v___y_1705_, v___y_1706_);
stack->m_obj
 = v_res_1709_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1710_, lean_object* v_declHint_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1710_, v_declHint_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1715_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1716_, lean_object* v_ref_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1717_ = stack[1].m_obj;
lean_object* v_msg_1718_ = stack[2].m_obj;
lean_object* v___y_1719_ = stack[3].m_obj;
lean_object* v___y_1720_ = stack[4].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_box(0), v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_ref_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1724_, v_ref_1725_, v_msg_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v_ref_1725_);
return v_res_1730_;
}
}
lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1744_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1745_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1746_ = lean_box(0);
v___x_1747_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1748_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1743_, v___x_1745_, v___x_1746_, v___x_1747_, v___x_1744_, v_ref_1741_);
return v___x_1748_;
}
}
LEAN_EXPORT void l_Lean_Elab_mkMacroAttributeUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1741_ = stack[0].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1741_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1750_);
return v_res_1752_;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1760_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1761_;
v_res_1761_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1763_;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1767_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1768_ = l_Lean_addBuiltinDocString(v___x_1766_, v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1769_;
v_res_1769_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
stack->m_obj
 = v_res_1769_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1771_;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1799_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1800_ = l_Lean_addBuiltinDeclarationRanges(v___x_1798_, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1801_;
v_res_1801_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
stack->m_obj
 = v_res_1801_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1804_, lean_object* v_a_1805_, lean_object* v_____r_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_declName_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1820_; 
v_declName_1809_ = lean_ctor_get(v_toOLeanEntry_1804_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_toOLeanEntry_1804_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v_toOLeanEntry_1804_, 0);
lean_dec(v_unused_1821_);
v___x_1811_ = v_toOLeanEntry_1804_;
v_isShared_1812_ = v_isSharedCheck_1820_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_declName_1809_);
lean_dec(v_toOLeanEntry_1804_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1820_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1805_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1813_);
lean_ctor_set(v___x_1811_, 0, v_declName_1809_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_declName_1809_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___y_1808_);
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1822_, lean_object* v_a_1823_, lean_object* v_____r_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1822_, v_a_1823_, v_____r_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1831_, lean_object* v_as_x27_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
if (lean_obj_tag(v_as_x27_1832_) == 0)
{
lean_object* v___x_1836_; 
lean_dec(v_stx_1831_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_b_1833_);
lean_ctor_set(v___x_1836_, 1, v___y_1835_);
return v___x_1836_;
}
else
{
lean_object* v_head_1837_; lean_object* v_tail_1838_; lean_object* v_toOLeanEntry_1839_; uint8_t v_isBuiltin_1840_; lean_object* v_value_1841_; lean_object* v_macroScope_1842_; lean_object* v_traceMsgs_1843_; lean_object* v_expandedMacroDecls_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_b_1833_);
v_head_1837_ = lean_ctor_get(v_as_x27_1832_, 0);
v_tail_1838_ = lean_ctor_get(v_as_x27_1832_, 1);
v_toOLeanEntry_1839_ = lean_ctor_get(v_head_1837_, 0);
v_isBuiltin_1840_ = lean_ctor_get_uint8(v_head_1837_, sizeof(void*)*2);
v_value_1841_ = lean_ctor_get(v_head_1837_, 1);
v_macroScope_1842_ = lean_ctor_get(v___y_1835_, 0);
v_traceMsgs_1843_ = lean_ctor_get(v___y_1835_, 1);
v_expandedMacroDecls_1844_ = lean_ctor_get(v___y_1835_, 2);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1835_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1846_ = v___y_1835_;
v_isShared_1847_ = v_isSharedCheck_1909_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_expandedMacroDecls_1844_);
lean_inc(v_traceMsgs_1843_);
lean_inc(v_macroScope_1842_);
lean_dec(v___y_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1909_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_methods_1848_; lean_object* v_quotContext_1849_; lean_object* v_currRecDepth_1850_; lean_object* v_maxRecDepth_1851_; lean_object* v_ref_1852_; lean_object* v___x_1853_; lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1860_; lean_object* v_a_1862_; lean_object* v_a_1863_; lean_object* v___y_1870_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v_methods_1848_ = lean_ctor_get(v___y_1834_, 0);
v_quotContext_1849_ = lean_ctor_get(v___y_1834_, 1);
v_currRecDepth_1850_ = lean_ctor_get(v___y_1834_, 3);
v_maxRecDepth_1851_ = lean_ctor_get(v___y_1834_, 4);
v_ref_1852_ = lean_ctor_get(v___y_1834_, 5);
v___x_1853_ = lean_box(0);
v___x_1860_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_add(v_macroScope_1842_, v___x_1876_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1877_);
v___x_1879_ = v___x_1846_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_traceMsgs_1843_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_expandedMacroDecls_1844_);
v___x_1879_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1878_;
}
v___jp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_a_1855_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1853_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v_a_1856_);
return v___x_1859_;
}
v___jp_1861_:
{
if (lean_obj_tag(v_a_1862_) == 1)
{
v_as_x27_1832_ = v_tail_1838_;
v_b_1833_ = v___x_1860_;
v___y_1835_ = v_a_1863_;
goto _start;
}
else
{
lean_object* v_declName_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec(v_stx_1831_);
v_declName_1865_ = lean_ctor_get(v_toOLeanEntry_1839_, 1);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1862_);
lean_inc(v_declName_1865_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_declName_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
v_a_1855_ = v___x_1868_;
v_a_1856_ = v_a_1863_;
goto v___jp_1854_;
}
}
v___jp_1869_:
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___y_1870_, 0);
if (lean_obj_tag(v_a_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v_a_1873_; 
lean_inc_ref(v_a_1871_);
lean_dec(v_stx_1831_);
v_a_1872_ = lean_ctor_get(v___y_1870_, 1);
lean_inc(v_a_1872_);
lean_dec_ref(v___y_1870_);
v_a_1873_ = lean_ctor_get(v_a_1871_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v_a_1871_, 1);
v_a_1855_ = v_a_1873_;
v_a_1856_ = v_a_1872_;
goto v___jp_1854_;
}
else
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___y_1870_, 1);
lean_inc(v_a_1874_);
lean_dec_ref(v___y_1870_);
v_as_x27_1832_ = v_tail_1838_;
v_b_1833_ = v___x_1860_;
v___y_1835_ = v_a_1874_;
goto _start;
}
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_inc(v_ref_1852_);
lean_inc(v_maxRecDepth_1851_);
lean_inc(v_currRecDepth_1850_);
lean_inc(v_quotContext_1849_);
lean_inc(v_methods_1848_);
v___x_1880_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1880_, 0, v_methods_1848_);
lean_ctor_set(v___x_1880_, 1, v_quotContext_1849_);
lean_ctor_set(v___x_1880_, 2, v_macroScope_1842_);
lean_ctor_set(v___x_1880_, 3, v_currRecDepth_1850_);
lean_ctor_set(v___x_1880_, 4, v_maxRecDepth_1851_);
lean_ctor_set(v___x_1880_, 5, v_ref_1852_);
lean_inc(v_value_1841_);
lean_inc(v_stx_1831_);
v___x_1881_ = lean_apply_3(v_value_1841_, v_stx_1831_, v___x_1880_, v___x_1879_);
if (lean_obj_tag(v___x_1881_) == 0)
{
if (v_isBuiltin_1840_ == 0)
{
lean_object* v_a_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1902_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 1);
v_a_1883_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1902_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1882_);
lean_inc(v_a_1883_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1902_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_macroScope_1887_; lean_object* v_traceMsgs_1888_; lean_object* v_expandedMacroDecls_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1901_; 
v_macroScope_1887_ = lean_ctor_get(v_a_1882_, 0);
v_traceMsgs_1888_ = lean_ctor_get(v_a_1882_, 1);
v_expandedMacroDecls_1889_ = lean_ctor_get(v_a_1882_, 2);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1882_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1891_ = v_a_1882_;
v_isShared_1892_ = v_isSharedCheck_1901_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_expandedMacroDecls_1889_);
lean_inc(v_traceMsgs_1888_);
lean_inc(v_macroScope_1887_);
lean_dec(v_a_1882_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1901_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_declName_1893_; lean_object* v___x_1895_; 
v_declName_1893_ = lean_ctor_get(v_toOLeanEntry_1839_, 1);
lean_inc(v_declName_1893_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 1);
lean_ctor_set(v___x_1885_, 1, v_expandedMacroDecls_1889_);
lean_ctor_set(v___x_1885_, 0, v_declName_1893_);
v___x_1895_ = v___x_1885_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_declName_1893_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_expandedMacroDecls_1889_);
v___x_1895_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v___x_1895_);
v___x_1897_ = v___x_1891_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_macroScope_1887_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_traceMsgs_1888_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
lean_inc_ref(v_toOLeanEntry_1839_);
v___x_1898_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1839_, v_a_1883_, v___x_1853_, v___y_1834_, v___x_1897_);
v___y_1870_ = v___x_1898_;
goto v___jp_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1903_);
v_a_1904_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1881_, 2);
lean_inc_ref(v_toOLeanEntry_1839_);
v___x_1905_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1839_, v_a_1903_, v___x_1853_, v___y_1834_, v_a_1904_);
v___y_1870_ = v___x_1905_;
goto v___jp_1869_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v_a_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1906_);
v_a_1907_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1881_, 2);
v_a_1862_ = v_a_1906_;
v_a_1863_ = v_a_1907_;
goto v___jp_1861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1910_, lean_object* v_as_x27_1911_, lean_object* v_b_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1910_, v_as_x27_1911_, v_b_1912_, v___y_1913_, v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v_as_x27_1911_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1916_, lean_object* v_stx_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v_fst_1927_; 
v___x_1920_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1917_);
v___x_1921_ = l_Lean_Syntax_getKind(v_stx_1917_);
v___x_1922_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1920_, v_env_1916_, v___x_1921_);
lean_dec(v___x_1921_);
v___x_1923_ = lean_box(0);
v___x_1924_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1925_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1917_, v___x_1922_, v___x_1924_, v_a_1918_, v_a_1919_);
lean_dec(v___x_1922_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_fst_1927_ = lean_ctor_get(v_a_1926_, 0);
if (lean_obj_tag(v_fst_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1925_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v___x_1925_, 0);
lean_dec(v_unused_1936_);
v___x_1930_ = v___x_1925_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1925_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1923_);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
lean_inc_ref(v_fst_1927_);
v_a_1937_ = lean_ctor_get(v___x_1925_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1925_, 0);
lean_dec(v_unused_1946_);
v___x_1939_ = v___x_1925_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1925_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_val_1941_; lean_object* v___x_1943_; 
v_val_1941_ = lean_ctor_get(v_fst_1927_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_fst_1927_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_val_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_val_1941_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1937_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1947_, lean_object* v_stx_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1947_, v_stx_1948_, v_a_1949_, v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1952_, lean_object* v_as_1953_, lean_object* v_as_x27_1954_, lean_object* v_b_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1952_, v_as_x27_1954_, v_b_1955_, v___y_1957_, v___y_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1960_, lean_object* v_as_1961_, lean_object* v_as_x27_1962_, lean_object* v_b_1963_, lean_object* v_a_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1960_, v_as_1961_, v_as_x27_1962_, v_b_1963_, v_a_1964_, v___y_1965_, v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v_as_x27_1962_);
lean_dec(v_as_1961_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1968_, lean_object* v_inst_1969_, lean_object* v_s_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_apply_1(v_setNextMacroScope_1968_, v_s_1970_);
v___x_1972_ = lean_apply_2(v_inst_1969_, lean_box(0), v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_){
_start:
{
lean_object* v_getNextMacroScope_1976_; lean_object* v_setNextMacroScope_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1986_; 
v_getNextMacroScope_1976_ = lean_ctor_get(v_inst_1975_, 1);
v_setNextMacroScope_1977_ = lean_ctor_get(v_inst_1975_, 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_inst_1975_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v_inst_1975_, 0);
lean_dec(v_unused_1987_);
v___x_1979_ = v_inst_1975_;
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_setNextMacroScope_1977_);
lean_inc(v_getNextMacroScope_1976_);
lean_dec(v_inst_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___f_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_inc(v_inst_1973_);
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1981_, 0, v_setNextMacroScope_1977_);
lean_closure_set(v___f_1981_, 1, v_inst_1973_);
v___x_1982_ = lean_apply_2(v_inst_1973_, lean_box(0), v_getNextMacroScope_1976_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 2, v___f_1981_);
lean_ctor_set(v___x_1979_, 1, v___x_1982_);
lean_ctor_set(v___x_1979_, 0, v_inst_1974_);
v___x_1984_ = v___x_1979_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_inst_1974_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v___f_1981_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1988_, lean_object* v_n_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_){
_start:
{
lean_object* v_getNextMacroScope_1993_; lean_object* v_setNextMacroScope_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v_getNextMacroScope_1993_ = lean_ctor_get(v_inst_1992_, 1);
v_setNextMacroScope_1994_ = lean_ctor_get(v_inst_1992_, 2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_inst_1992_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_inst_1992_, 0);
lean_dec(v_unused_2004_);
v___x_1996_ = v_inst_1992_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_setNextMacroScope_1994_);
lean_inc(v_getNextMacroScope_1993_);
lean_dec(v_inst_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___f_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_inc(v_inst_1990_);
v___f_1998_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1998_, 0, v_setNextMacroScope_1994_);
lean_closure_set(v___f_1998_, 1, v_inst_1990_);
v___x_1999_ = lean_apply_2(v_inst_1990_, lean_box(0), v_getNextMacroScope_1993_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 2, v___f_1998_);
lean_ctor_set(v___x_1996_, 1, v___x_1999_);
lean_ctor_set(v___x_1996_, 0, v_inst_1991_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_inst_1991_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v___f_1998_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_2005_, lean_object* v_fst_2006_, lean_object* v_____do__lift_2007_, lean_object* v_____do__lift_2008_){
_start:
{
uint8_t v_hasTrace_2009_; 
v_hasTrace_2009_ = lean_ctor_get_uint8(v_____do__lift_2008_, sizeof(void*)*1);
if (v_hasTrace_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_dec(v_fst_2006_);
v___x_2010_ = lean_box(v_hasTrace_2009_);
v___x_2011_ = lean_apply_2(v_toPure_2005_, lean_box(0), v___x_2010_);
return v___x_2011_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_2013_ = l_Lean_Name_append(v___x_2012_, v_fst_2006_);
v___x_2014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2007_, v_____do__lift_2008_, v___x_2013_);
lean_dec(v___x_2013_);
v___x_2015_ = lean_box(v___x_2014_);
v___x_2016_ = lean_apply_2(v_toPure_2005_, lean_box(0), v___x_2015_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_2017_, lean_object* v_fst_2018_, lean_object* v_____do__lift_2019_, lean_object* v_____do__lift_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_2017_, v_fst_2018_, v_____do__lift_2019_, v_____do__lift_2020_);
lean_dec_ref(v_____do__lift_2020_);
lean_dec_ref(v_____do__lift_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_inst_2022_, lean_object* v_toPure_2023_, lean_object* v_fst_2024_, lean_object* v_toBind_2025_, lean_object* v_____do__lift_2026_){
_start:
{
lean_object* v_getOptionsUnrestricted_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v_getOptionsUnrestricted_2027_ = lean_ctor_get(v_inst_2022_, 1);
lean_inc(v_getOptionsUnrestricted_2027_);
lean_dec_ref(v_inst_2022_);
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2028_, 0, v_toPure_2023_);
lean_closure_set(v___f_2028_, 1, v_fst_2024_);
lean_closure_set(v___f_2028_, 2, v_____do__lift_2026_);
v___x_2029_ = lean_apply_4(v_toBind_2025_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2027_, v___f_2028_);
return v___x_2029_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_2030_, lean_object* v_snd_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_toMonadRef_2034_, lean_object* v_inst_2035_, lean_object* v_fst_2036_, uint8_t v_____do__lift_2037_){
_start:
{
if (v_____do__lift_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_fst_2036_);
lean_dec(v_inst_2035_);
lean_dec_ref(v_toMonadRef_2034_);
lean_dec_ref(v_inst_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_snd_2031_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_apply_2(v_toPure_2030_, lean_box(0), v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec(v_toPure_2030_);
v___x_2040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_snd_2031_);
v___x_2041_ = l_Lean_MessageData_ofFormat(v___x_2040_);
v___x_2042_ = l_Lean_addTrace___redArg(v_inst_2032_, v_inst_2033_, v_toMonadRef_2034_, v_inst_2035_, v_fst_2036_, v___x_2041_);
return v___x_2042_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2030_ = stack[0].m_obj;
lean_object* v_snd_2031_ = stack[1].m_obj;
lean_object* v_inst_2032_ = stack[2].m_obj;
lean_object* v_inst_2033_ = stack[3].m_obj;
lean_object* v_toMonadRef_2034_ = stack[4].m_obj;
lean_object* v_inst_2035_ = stack[5].m_obj;
lean_object* v_fst_2036_ = stack[6].m_obj;
uint8_t v_____do__lift_2037_ = stack[7].m_num;
lean_object* v_res_2043_;
v_res_2043_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_toPure_2030_, v_snd_2031_, v_inst_2032_, v_inst_2033_, v_toMonadRef_2034_, v_inst_2035_, v_fst_2036_, v_____do__lift_2037_);
stack->m_obj
 = v_res_2043_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object* v_toPure_2044_, lean_object* v_snd_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_toMonadRef_2048_, lean_object* v_inst_2049_, lean_object* v_fst_2050_, lean_object* v_____do__lift_2051_){
_start:
{
uint8_t v_____do__lift_1462__boxed_2052_; lean_object* v_res_2053_; 
v_____do__lift_1462__boxed_2052_ = lean_unbox(v_____do__lift_2051_);
v_res_2053_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_toPure_2044_, v_snd_2045_, v_inst_2046_, v_inst_2047_, v_toMonadRef_2048_, v_inst_2049_, v_fst_2050_, v_____do__lift_1462__boxed_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_toPure_2056_, lean_object* v_toBind_2057_, lean_object* v_inst_2058_, lean_object* v_toMonadRef_2059_, lean_object* v_inst_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v_fst_2062_; lean_object* v_snd_2063_; lean_object* v_getInheritedTraceOptions_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_fst_2062_ = lean_ctor_get(v_x_2061_, 0);
lean_inc_n(v_fst_2062_, 2);
v_snd_2063_ = lean_ctor_get(v_x_2061_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v_x_2061_);
v_getInheritedTraceOptions_2064_ = lean_ctor_get(v_inst_2054_, 2);
lean_inc(v_getInheritedTraceOptions_2064_);
lean_inc_n(v_toBind_2057_, 2);
lean_inc(v_toPure_2056_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2065_, 0, v_inst_2055_);
lean_closure_set(v___f_2065_, 1, v_toPure_2056_);
lean_closure_set(v___f_2065_, 2, v_fst_2062_);
lean_closure_set(v___f_2065_, 3, v_toBind_2057_);
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2066_, 0, v_toPure_2056_);
lean_closure_set(v___f_2066_, 1, v_snd_2063_);
lean_closure_set(v___f_2066_, 2, v_inst_2058_);
lean_closure_set(v___f_2066_, 3, v_inst_2054_);
lean_closure_set(v___f_2066_, 4, v_toMonadRef_2059_);
lean_closure_set(v___f_2066_, 5, v_inst_2060_);
lean_closure_set(v___f_2066_, 6, v_fst_2062_);
v___x_2067_ = lean_apply_4(v_toBind_2057_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2064_, v___f_2065_);
v___x_2068_ = lean_apply_4(v_toBind_2057_, lean_box(0), lean_box(0), v___x_2067_, v___f_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_2069_, lean_object* v___x_2070_, lean_object* v___x_2071_, lean_object* v_stx_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2069_, v_stx_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
if (lean_obj_tag(v_a_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v___x_2071_);
lean_dec_ref(v___x_2070_);
v_a_2077_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2075_, 0);
lean_dec(v_unused_2086_);
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2085_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_a_2077_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2117_; 
v_val_2087_ = lean_ctor_get(v_a_2076_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2076_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2089_ = v_a_2076_;
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v_a_2076_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_snd_2091_; 
v_snd_2091_ = lean_ctor_get(v_val_2087_, 1);
lean_inc(v_snd_2091_);
lean_dec(v_val_2087_);
if (lean_obj_tag(v_snd_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_2089_);
v_a_2092_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2075_, 2);
v_a_2093_ = lean_ctor_get(v_snd_2091_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_snd_2091_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2095_ = v_snd_2091_;
v_isShared_2096_ = v_isSharedCheck_2102_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v_snd_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2102_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_1186__overap_2099_; lean_object* v___x_2100_; 
v___x_1186__overap_2099_ = l_liftExcept___redArg(v___x_2070_, v___x_2071_, v___x_2098_);
lean_inc_ref(v___y_2073_);
v___x_2100_ = lean_apply_2(v___x_1186__overap_2099_, v___y_2073_, v_a_2092_);
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2116_; 
v_a_2103_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2075_, 2);
v_a_2104_ = lean_ctor_get(v_snd_2091_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_snd_2091_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2106_ = v_snd_2091_;
v_isShared_2107_ = v_isSharedCheck_2116_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v_snd_2091_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2116_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_a_2104_);
v___x_2109_ = v___x_2089_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2109_);
v___x_2111_ = v___x_2106_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_1190__overap_2112_; lean_object* v___x_2113_; 
v___x_1190__overap_2112_ = l_liftExcept___redArg(v___x_2070_, v___x_2071_, v___x_2111_);
lean_inc_ref(v___y_2073_);
v___x_2113_ = lean_apply_2(v___x_1190__overap_2112_, v___y_2073_, v_a_2103_);
return v___x_2113_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v___x_2071_);
lean_dec_ref(v___x_2070_);
v_a_2118_ = lean_ctor_get(v___x_2075_, 0);
v_a_2119_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2075_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_inc(v_a_2118_);
lean_dec(v___x_2075_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2118_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2127_, lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v_stx_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2127_, v___x_2128_, v___x_2129_, v_stx_2130_, v___y_2131_, v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2134_, lean_object* v_declName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_2138_; lean_object* v_env_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2138_ = 0;
v_env_2139_ = l_Lean_Environment_setExporting(v_env_2134_, v___x_2138_);
lean_inc(v_declName_2135_);
v___x_2140_ = l_Lean_mkPrivateName(v_env_2139_, v_declName_2135_);
v___x_2141_ = 1;
lean_inc_ref(v_env_2139_);
v___x_2142_ = l_Lean_Environment_contains(v_env_2139_, v___x_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2143_ = l_Lean_privateToUserName(v_declName_2135_);
v___x_2144_ = l_Lean_Environment_contains(v_env_2139_, v___x_2143_, v___x_2141_);
v___x_2145_ = lean_box(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v___y_2137_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v_env_2139_);
lean_dec(v_declName_2135_);
v___x_2147_ = lean_box(v___x_2142_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v___y_2137_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2149_, lean_object* v_declName_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2149_, v_declName_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2154_, lean_object* v_currNamespace_2155_, lean_object* v_openDecls_2156_, lean_object* v_n_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = l_Lean_ResolveName_resolveNamespace(v_env_2154_, v_currNamespace_2155_, v_openDecls_2156_, v_n_2157_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___y_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2162_, lean_object* v_currNamespace_2163_, lean_object* v_openDecls_2164_, lean_object* v_n_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2162_, v_currNamespace_2163_, v_openDecls_2164_, v_n_2165_, v___y_2166_, v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2169_, lean_object* v_opts_2170_, lean_object* v_currNamespace_2171_, lean_object* v_openDecls_2172_, lean_object* v_n_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = l_Lean_ResolveName_resolveGlobalName(v_env_2169_, v_opts_2170_, v_currNamespace_2171_, v_openDecls_2172_, v_n_2173_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2178_, lean_object* v_opts_2179_, lean_object* v_currNamespace_2180_, lean_object* v_openDecls_2181_, lean_object* v_n_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2178_, v_opts_2179_, v_currNamespace_2180_, v_openDecls_2181_, v_n_2182_, v___y_2183_, v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec_ref(v_opts_2179_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2186_, lean_object* v_a_2187_, lean_object* v_____r_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_apply_2(v_toPure_2186_, lean_box(0), v_a_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2190_, lean_object* v_inst_2191_, lean_object* v___f_2192_, lean_object* v_toBind_2193_, lean_object* v___f_2194_, lean_object* v_____r_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = l_List_reverse___redArg(v_traceMsgs_2190_);
v___x_2197_ = l_List_forM___redArg(v_inst_2191_, v___x_2196_, v___f_2192_);
v___x_2198_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2197_, v___f_2194_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2199_, lean_object* v_macroScope_2200_, lean_object* v_toBind_2201_, lean_object* v___f_2202_, lean_object* v_____s_2203_){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_apply_1(v_setNextMacroScope_2199_, v_macroScope_2200_);
v___x_2205_ = lean_apply_4(v_toBind_2201_, lean_box(0), lean_box(0), v___x_2204_, v___f_2202_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2206_, lean_object* v_toPure_2207_, lean_object* v_____r_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
v___x_2210_ = lean_apply_2(v_toPure_2207_, lean_box(0), v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_toMonadRef_2215_, lean_object* v_inst_2216_, lean_object* v_toBind_2217_, lean_object* v___f_2218_, lean_object* v_a_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = 1;
v___x_2223_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2211_, v_inst_2212_, v_inst_2213_, v_inst_2214_, v_toMonadRef_2215_, v_inst_2216_, v_a_2219_, v___x_2222_);
v___x_2224_ = lean_apply_4(v_toBind_2217_, lean_box(0), lean_box(0), v___x_2223_, v___f_2218_);
return v___x_2224_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2226_, lean_object* v_____do__lift_2227_, lean_object* v_____do__lift_2228_, lean_object* v_____do__lift_2229_, lean_object* v_____do__lift_2230_, lean_object* v_____do__lift_2231_, lean_object* v_x_2232_, lean_object* v_toPure_2233_, lean_object* v_inst_2234_, lean_object* v___f_2235_, lean_object* v_toBind_2236_, lean_object* v_setNextMacroScope_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_toMonadRef_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_toMonadExceptOf_2244_, lean_object* v_____do__lift_2245_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2246_, 0, v_methods_2226_);
lean_ctor_set(v___x_2246_, 1, v_____do__lift_2227_);
lean_ctor_set(v___x_2246_, 2, v_____do__lift_2228_);
lean_ctor_set(v___x_2246_, 3, v_____do__lift_2229_);
lean_ctor_set(v___x_2246_, 4, v_____do__lift_2230_);
lean_ctor_set(v___x_2246_, 5, v_____do__lift_2231_);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2248_, 0, v_____do__lift_2245_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
v___x_2249_ = lean_apply_2(v_x_2232_, v___x_2246_, v___x_2248_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v_macroScope_2252_; lean_object* v_traceMsgs_2253_; lean_object* v_expandedMacroDecls_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v_toMonadExceptOf_2244_);
lean_dec_ref(v_inst_2243_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_a_2250_);
v_a_2251_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2249_, 2);
v_macroScope_2252_ = lean_ctor_get(v_a_2250_, 0);
lean_inc(v_macroScope_2252_);
v_traceMsgs_2253_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_traceMsgs_2253_);
v_expandedMacroDecls_2254_ = lean_ctor_get(v_a_2250_, 2);
lean_inc(v_expandedMacroDecls_2254_);
lean_dec(v_a_2250_);
lean_inc(v_toPure_2233_);
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2255_, 0, v_toPure_2233_);
lean_closure_set(v___f_2255_, 1, v_a_2251_);
lean_inc_n(v_toBind_2236_, 3);
lean_inc_ref_n(v_inst_2234_, 2);
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2256_, 0, v_traceMsgs_2253_);
lean_closure_set(v___f_2256_, 1, v_inst_2234_);
lean_closure_set(v___f_2256_, 2, v___f_2235_);
lean_closure_set(v___f_2256_, 3, v_toBind_2236_);
lean_closure_set(v___f_2256_, 4, v___f_2255_);
v___f_2257_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2257_, 0, v_setNextMacroScope_2237_);
lean_closure_set(v___f_2257_, 1, v_macroScope_2252_);
lean_closure_set(v___f_2257_, 2, v_toBind_2236_);
lean_closure_set(v___f_2257_, 3, v___f_2256_);
v___x_2258_ = lean_box(0);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2259_, 0, v___x_2258_);
lean_closure_set(v___f_2259_, 1, v_toPure_2233_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2260_, 0, v_inst_2234_);
lean_closure_set(v___f_2260_, 1, v_inst_2238_);
lean_closure_set(v___f_2260_, 2, v_inst_2239_);
lean_closure_set(v___f_2260_, 3, v_inst_2240_);
lean_closure_set(v___f_2260_, 4, v_toMonadRef_2241_);
lean_closure_set(v___f_2260_, 5, v_inst_2242_);
lean_closure_set(v___f_2260_, 6, v_toBind_2236_);
lean_closure_set(v___f_2260_, 7, v___f_2259_);
v___x_2261_ = l_List_forIn_x27_loop___redArg(v_inst_2234_, v___f_2260_, v_expandedMacroDecls_2254_, v___x_2258_);
lean_dec(v_expandedMacroDecls_2254_);
v___x_2262_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2261_, v___f_2257_);
return v___x_2262_;
}
else
{
lean_object* v_a_2263_; 
lean_dec(v_inst_2242_);
lean_dec_ref(v_toMonadRef_2241_);
lean_dec_ref(v_inst_2240_);
lean_dec_ref(v_inst_2239_);
lean_dec_ref(v_inst_2238_);
lean_dec(v_setNextMacroScope_2237_);
lean_dec(v_toBind_2236_);
lean_dec(v___f_2235_);
lean_dec(v_toPure_2233_);
v_a_2263_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2249_, 2);
if (lean_obj_tag(v_a_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
lean_dec_ref(v_toMonadExceptOf_2244_);
v_a_2264_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_a_2264_);
v_a_2265_ = lean_ctor_get(v_a_2263_, 1);
lean_inc_ref(v_a_2265_);
lean_dec_ref_known(v_a_2263_, 2);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2267_ = lean_string_dec_eq(v_a_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_a_2265_);
v___x_2269_ = l_Lean_MessageData_ofFormat(v___x_2268_);
v___x_2270_ = l_Lean_throwErrorAt___redArg(v_inst_2234_, v_inst_2243_, v_a_2264_, v___x_2269_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_inst_2234_);
v___x_2271_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2243_, v_a_2264_);
return v___x_2271_;
}
}
else
{
lean_object* v___x_2272_; 
lean_dec_ref(v_inst_2243_);
lean_dec_ref(v_inst_2234_);
v___x_2272_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2244_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_2226_ = stack[0].m_obj;
lean_object* v_____do__lift_2227_ = stack[1].m_obj;
lean_object* v_____do__lift_2228_ = stack[2].m_obj;
lean_object* v_____do__lift_2229_ = stack[3].m_obj;
lean_object* v_____do__lift_2230_ = stack[4].m_obj;
lean_object* v_____do__lift_2231_ = stack[5].m_obj;
lean_object* v_x_2232_ = stack[6].m_obj;
lean_object* v_toPure_2233_ = stack[7].m_obj;
lean_object* v_inst_2234_ = stack[8].m_obj;
lean_object* v___f_2235_ = stack[9].m_obj;
lean_object* v_toBind_2236_ = stack[10].m_obj;
lean_object* v_setNextMacroScope_2237_ = stack[11].m_obj;
lean_object* v_inst_2238_ = stack[12].m_obj;
lean_object* v_inst_2239_ = stack[13].m_obj;
lean_object* v_inst_2240_ = stack[14].m_obj;
lean_object* v_toMonadRef_2241_ = stack[15].m_obj;
lean_object* v_inst_2242_ = stack[16].m_obj;
lean_object* v_inst_2243_ = stack[17].m_obj;
lean_object* v_toMonadExceptOf_2244_ = stack[18].m_obj;
lean_object* v_____do__lift_2245_ = stack[19].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2226_, v_____do__lift_2227_, v_____do__lift_2228_, v_____do__lift_2229_, v_____do__lift_2230_, v_____do__lift_2231_, v_x_2232_, v_toPure_2233_, v_inst_2234_, v___f_2235_, v_toBind_2236_, v_setNextMacroScope_2237_, v_inst_2238_, v_inst_2239_, v_inst_2240_, v_toMonadRef_2241_, v_inst_2242_, v_inst_2243_, v_toMonadExceptOf_2244_, v_____do__lift_2245_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2274_ = _args[0];
lean_object* v_____do__lift_2275_ = _args[1];
lean_object* v_____do__lift_2276_ = _args[2];
lean_object* v_____do__lift_2277_ = _args[3];
lean_object* v_____do__lift_2278_ = _args[4];
lean_object* v_____do__lift_2279_ = _args[5];
lean_object* v_x_2280_ = _args[6];
lean_object* v_toPure_2281_ = _args[7];
lean_object* v_inst_2282_ = _args[8];
lean_object* v___f_2283_ = _args[9];
lean_object* v_toBind_2284_ = _args[10];
lean_object* v_setNextMacroScope_2285_ = _args[11];
lean_object* v_inst_2286_ = _args[12];
lean_object* v_inst_2287_ = _args[13];
lean_object* v_inst_2288_ = _args[14];
lean_object* v_toMonadRef_2289_ = _args[15];
lean_object* v_inst_2290_ = _args[16];
lean_object* v_inst_2291_ = _args[17];
lean_object* v_toMonadExceptOf_2292_ = _args[18];
lean_object* v_____do__lift_2293_ = _args[19];
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2274_, v_____do__lift_2275_, v_____do__lift_2276_, v_____do__lift_2277_, v_____do__lift_2278_, v_____do__lift_2279_, v_x_2280_, v_toPure_2281_, v_inst_2282_, v___f_2283_, v_toBind_2284_, v_setNextMacroScope_2285_, v_inst_2286_, v_inst_2287_, v_inst_2288_, v_toMonadRef_2289_, v_inst_2290_, v_inst_2291_, v_toMonadExceptOf_2292_, v_____do__lift_2293_);
return v_res_2294_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2295_, lean_object* v_____do__lift_2296_, lean_object* v_____do__lift_2297_, lean_object* v_____do__lift_2298_, lean_object* v_____do__lift_2299_, lean_object* v_x_2300_, lean_object* v_toPure_2301_, lean_object* v_inst_2302_, lean_object* v___f_2303_, lean_object* v_toBind_2304_, lean_object* v_setNextMacroScope_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_toMonadRef_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_toMonadExceptOf_2312_, lean_object* v_getNextMacroScope_2313_, lean_object* v_____do__lift_2314_){
_start:
{
lean_object* v___f_2315_; lean_object* v___x_2316_; 
lean_inc(v_toBind_2304_);
v___f_2315_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2315_, 0, v_methods_2295_);
lean_closure_set(v___f_2315_, 1, v_____do__lift_2296_);
lean_closure_set(v___f_2315_, 2, v_____do__lift_2297_);
lean_closure_set(v___f_2315_, 3, v_____do__lift_2298_);
lean_closure_set(v___f_2315_, 4, v_____do__lift_2314_);
lean_closure_set(v___f_2315_, 5, v_____do__lift_2299_);
lean_closure_set(v___f_2315_, 6, v_x_2300_);
lean_closure_set(v___f_2315_, 7, v_toPure_2301_);
lean_closure_set(v___f_2315_, 8, v_inst_2302_);
lean_closure_set(v___f_2315_, 9, v___f_2303_);
lean_closure_set(v___f_2315_, 10, v_toBind_2304_);
lean_closure_set(v___f_2315_, 11, v_setNextMacroScope_2305_);
lean_closure_set(v___f_2315_, 12, v_inst_2306_);
lean_closure_set(v___f_2315_, 13, v_inst_2307_);
lean_closure_set(v___f_2315_, 14, v_inst_2308_);
lean_closure_set(v___f_2315_, 15, v_toMonadRef_2309_);
lean_closure_set(v___f_2315_, 16, v_inst_2310_);
lean_closure_set(v___f_2315_, 17, v_inst_2311_);
lean_closure_set(v___f_2315_, 18, v_toMonadExceptOf_2312_);
v___x_2316_ = lean_apply_4(v_toBind_2304_, lean_box(0), lean_box(0), v_getNextMacroScope_2313_, v___f_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_2295_ = stack[0].m_obj;
lean_object* v_____do__lift_2296_ = stack[1].m_obj;
lean_object* v_____do__lift_2297_ = stack[2].m_obj;
lean_object* v_____do__lift_2298_ = stack[3].m_obj;
lean_object* v_____do__lift_2299_ = stack[4].m_obj;
lean_object* v_x_2300_ = stack[5].m_obj;
lean_object* v_toPure_2301_ = stack[6].m_obj;
lean_object* v_inst_2302_ = stack[7].m_obj;
lean_object* v___f_2303_ = stack[8].m_obj;
lean_object* v_toBind_2304_ = stack[9].m_obj;
lean_object* v_setNextMacroScope_2305_ = stack[10].m_obj;
lean_object* v_inst_2306_ = stack[11].m_obj;
lean_object* v_inst_2307_ = stack[12].m_obj;
lean_object* v_inst_2308_ = stack[13].m_obj;
lean_object* v_toMonadRef_2309_ = stack[14].m_obj;
lean_object* v_inst_2310_ = stack[15].m_obj;
lean_object* v_inst_2311_ = stack[16].m_obj;
lean_object* v_toMonadExceptOf_2312_ = stack[17].m_obj;
lean_object* v_getNextMacroScope_2313_ = stack[18].m_obj;
lean_object* v_____do__lift_2314_ = stack[19].m_obj;
lean_object* v_res_2317_;
v_res_2317_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2295_, v_____do__lift_2296_, v_____do__lift_2297_, v_____do__lift_2298_, v_____do__lift_2299_, v_x_2300_, v_toPure_2301_, v_inst_2302_, v___f_2303_, v_toBind_2304_, v_setNextMacroScope_2305_, v_inst_2306_, v_inst_2307_, v_inst_2308_, v_toMonadRef_2309_, v_inst_2310_, v_inst_2311_, v_toMonadExceptOf_2312_, v_getNextMacroScope_2313_, v_____do__lift_2314_);
stack->m_obj
 = v_res_2317_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2318_ = _args[0];
lean_object* v_____do__lift_2319_ = _args[1];
lean_object* v_____do__lift_2320_ = _args[2];
lean_object* v_____do__lift_2321_ = _args[3];
lean_object* v_____do__lift_2322_ = _args[4];
lean_object* v_x_2323_ = _args[5];
lean_object* v_toPure_2324_ = _args[6];
lean_object* v_inst_2325_ = _args[7];
lean_object* v___f_2326_ = _args[8];
lean_object* v_toBind_2327_ = _args[9];
lean_object* v_setNextMacroScope_2328_ = _args[10];
lean_object* v_inst_2329_ = _args[11];
lean_object* v_inst_2330_ = _args[12];
lean_object* v_inst_2331_ = _args[13];
lean_object* v_toMonadRef_2332_ = _args[14];
lean_object* v_inst_2333_ = _args[15];
lean_object* v_inst_2334_ = _args[16];
lean_object* v_toMonadExceptOf_2335_ = _args[17];
lean_object* v_getNextMacroScope_2336_ = _args[18];
lean_object* v_____do__lift_2337_ = _args[19];
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2318_, v_____do__lift_2319_, v_____do__lift_2320_, v_____do__lift_2321_, v_____do__lift_2322_, v_x_2323_, v_toPure_2324_, v_inst_2325_, v___f_2326_, v_toBind_2327_, v_setNextMacroScope_2328_, v_inst_2329_, v_inst_2330_, v_inst_2331_, v_toMonadRef_2332_, v_inst_2333_, v_inst_2334_, v_toMonadExceptOf_2335_, v_getNextMacroScope_2336_, v_____do__lift_2337_);
return v_res_2338_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2339_, lean_object* v_____do__lift_2340_, lean_object* v_____do__lift_2341_, lean_object* v_____do__lift_2342_, lean_object* v_x_2343_, lean_object* v_toPure_2344_, lean_object* v_inst_2345_, lean_object* v___f_2346_, lean_object* v_toBind_2347_, lean_object* v_setNextMacroScope_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_toMonadRef_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_toMonadExceptOf_2355_, lean_object* v_getNextMacroScope_2356_, lean_object* v_getMaxRecDepth_2357_, lean_object* v_____do__lift_2358_){
_start:
{
lean_object* v___f_2359_; lean_object* v___x_2360_; 
lean_inc(v_toBind_2347_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2359_, 0, v_methods_2339_);
lean_closure_set(v___f_2359_, 1, v_____do__lift_2340_);
lean_closure_set(v___f_2359_, 2, v_____do__lift_2341_);
lean_closure_set(v___f_2359_, 3, v_____do__lift_2358_);
lean_closure_set(v___f_2359_, 4, v_____do__lift_2342_);
lean_closure_set(v___f_2359_, 5, v_x_2343_);
lean_closure_set(v___f_2359_, 6, v_toPure_2344_);
lean_closure_set(v___f_2359_, 7, v_inst_2345_);
lean_closure_set(v___f_2359_, 8, v___f_2346_);
lean_closure_set(v___f_2359_, 9, v_toBind_2347_);
lean_closure_set(v___f_2359_, 10, v_setNextMacroScope_2348_);
lean_closure_set(v___f_2359_, 11, v_inst_2349_);
lean_closure_set(v___f_2359_, 12, v_inst_2350_);
lean_closure_set(v___f_2359_, 13, v_inst_2351_);
lean_closure_set(v___f_2359_, 14, v_toMonadRef_2352_);
lean_closure_set(v___f_2359_, 15, v_inst_2353_);
lean_closure_set(v___f_2359_, 16, v_inst_2354_);
lean_closure_set(v___f_2359_, 17, v_toMonadExceptOf_2355_);
lean_closure_set(v___f_2359_, 18, v_getNextMacroScope_2356_);
v___x_2360_ = lean_apply_4(v_toBind_2347_, lean_box(0), lean_box(0), v_getMaxRecDepth_2357_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_methods_2339_ = stack[0].m_obj;
lean_object* v_____do__lift_2340_ = stack[1].m_obj;
lean_object* v_____do__lift_2341_ = stack[2].m_obj;
lean_object* v_____do__lift_2342_ = stack[3].m_obj;
lean_object* v_x_2343_ = stack[4].m_obj;
lean_object* v_toPure_2344_ = stack[5].m_obj;
lean_object* v_inst_2345_ = stack[6].m_obj;
lean_object* v___f_2346_ = stack[7].m_obj;
lean_object* v_toBind_2347_ = stack[8].m_obj;
lean_object* v_setNextMacroScope_2348_ = stack[9].m_obj;
lean_object* v_inst_2349_ = stack[10].m_obj;
lean_object* v_inst_2350_ = stack[11].m_obj;
lean_object* v_inst_2351_ = stack[12].m_obj;
lean_object* v_toMonadRef_2352_ = stack[13].m_obj;
lean_object* v_inst_2353_ = stack[14].m_obj;
lean_object* v_inst_2354_ = stack[15].m_obj;
lean_object* v_toMonadExceptOf_2355_ = stack[16].m_obj;
lean_object* v_getNextMacroScope_2356_ = stack[17].m_obj;
lean_object* v_getMaxRecDepth_2357_ = stack[18].m_obj;
lean_object* v_____do__lift_2358_ = stack[19].m_obj;
lean_object* v_res_2361_;
v_res_2361_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2339_, v_____do__lift_2340_, v_____do__lift_2341_, v_____do__lift_2342_, v_x_2343_, v_toPure_2344_, v_inst_2345_, v___f_2346_, v_toBind_2347_, v_setNextMacroScope_2348_, v_inst_2349_, v_inst_2350_, v_inst_2351_, v_toMonadRef_2352_, v_inst_2353_, v_inst_2354_, v_toMonadExceptOf_2355_, v_getNextMacroScope_2356_, v_getMaxRecDepth_2357_, v_____do__lift_2358_);
stack->m_obj
 = v_res_2361_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2362_ = _args[0];
lean_object* v_____do__lift_2363_ = _args[1];
lean_object* v_____do__lift_2364_ = _args[2];
lean_object* v_____do__lift_2365_ = _args[3];
lean_object* v_x_2366_ = _args[4];
lean_object* v_toPure_2367_ = _args[5];
lean_object* v_inst_2368_ = _args[6];
lean_object* v___f_2369_ = _args[7];
lean_object* v_toBind_2370_ = _args[8];
lean_object* v_setNextMacroScope_2371_ = _args[9];
lean_object* v_inst_2372_ = _args[10];
lean_object* v_inst_2373_ = _args[11];
lean_object* v_inst_2374_ = _args[12];
lean_object* v_toMonadRef_2375_ = _args[13];
lean_object* v_inst_2376_ = _args[14];
lean_object* v_inst_2377_ = _args[15];
lean_object* v_toMonadExceptOf_2378_ = _args[16];
lean_object* v_getNextMacroScope_2379_ = _args[17];
lean_object* v_getMaxRecDepth_2380_ = _args[18];
lean_object* v_____do__lift_2381_ = _args[19];
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2362_, v_____do__lift_2363_, v_____do__lift_2364_, v_____do__lift_2365_, v_x_2366_, v_toPure_2367_, v_inst_2368_, v___f_2369_, v_toBind_2370_, v_setNextMacroScope_2371_, v_inst_2372_, v_inst_2373_, v_inst_2374_, v_toMonadRef_2375_, v_inst_2376_, v_inst_2377_, v_toMonadExceptOf_2378_, v_getNextMacroScope_2379_, v_getMaxRecDepth_2380_, v_____do__lift_2381_);
return v_res_2382_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2383_, lean_object* v_methods_2384_, lean_object* v_____do__lift_2385_, lean_object* v_____do__lift_2386_, lean_object* v_x_2387_, lean_object* v_toPure_2388_, lean_object* v_inst_2389_, lean_object* v___f_2390_, lean_object* v_toBind_2391_, lean_object* v_setNextMacroScope_2392_, lean_object* v_inst_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_toMonadRef_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_toMonadExceptOf_2399_, lean_object* v_getNextMacroScope_2400_, lean_object* v_____do__lift_2401_){
_start:
{
lean_object* v_getRecDepth_2402_; lean_object* v_getMaxRecDepth_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; 
v_getRecDepth_2402_ = lean_ctor_get(v_inst_2383_, 1);
lean_inc(v_getRecDepth_2402_);
v_getMaxRecDepth_2403_ = lean_ctor_get(v_inst_2383_, 2);
lean_inc(v_getMaxRecDepth_2403_);
lean_dec_ref(v_inst_2383_);
lean_inc(v_toBind_2391_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2404_, 0, v_methods_2384_);
lean_closure_set(v___f_2404_, 1, v_____do__lift_2401_);
lean_closure_set(v___f_2404_, 2, v_____do__lift_2385_);
lean_closure_set(v___f_2404_, 3, v_____do__lift_2386_);
lean_closure_set(v___f_2404_, 4, v_x_2387_);
lean_closure_set(v___f_2404_, 5, v_toPure_2388_);
lean_closure_set(v___f_2404_, 6, v_inst_2389_);
lean_closure_set(v___f_2404_, 7, v___f_2390_);
lean_closure_set(v___f_2404_, 8, v_toBind_2391_);
lean_closure_set(v___f_2404_, 9, v_setNextMacroScope_2392_);
lean_closure_set(v___f_2404_, 10, v_inst_2393_);
lean_closure_set(v___f_2404_, 11, v_inst_2394_);
lean_closure_set(v___f_2404_, 12, v_inst_2395_);
lean_closure_set(v___f_2404_, 13, v_toMonadRef_2396_);
lean_closure_set(v___f_2404_, 14, v_inst_2397_);
lean_closure_set(v___f_2404_, 15, v_inst_2398_);
lean_closure_set(v___f_2404_, 16, v_toMonadExceptOf_2399_);
lean_closure_set(v___f_2404_, 17, v_getNextMacroScope_2400_);
lean_closure_set(v___f_2404_, 18, v_getMaxRecDepth_2403_);
v___x_2405_ = lean_apply_4(v_toBind_2391_, lean_box(0), lean_box(0), v_getRecDepth_2402_, v___f_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2383_ = stack[0].m_obj;
lean_object* v_methods_2384_ = stack[1].m_obj;
lean_object* v_____do__lift_2385_ = stack[2].m_obj;
lean_object* v_____do__lift_2386_ = stack[3].m_obj;
lean_object* v_x_2387_ = stack[4].m_obj;
lean_object* v_toPure_2388_ = stack[5].m_obj;
lean_object* v_inst_2389_ = stack[6].m_obj;
lean_object* v___f_2390_ = stack[7].m_obj;
lean_object* v_toBind_2391_ = stack[8].m_obj;
lean_object* v_setNextMacroScope_2392_ = stack[9].m_obj;
lean_object* v_inst_2393_ = stack[10].m_obj;
lean_object* v_inst_2394_ = stack[11].m_obj;
lean_object* v_inst_2395_ = stack[12].m_obj;
lean_object* v_toMonadRef_2396_ = stack[13].m_obj;
lean_object* v_inst_2397_ = stack[14].m_obj;
lean_object* v_inst_2398_ = stack[15].m_obj;
lean_object* v_toMonadExceptOf_2399_ = stack[16].m_obj;
lean_object* v_getNextMacroScope_2400_ = stack[17].m_obj;
lean_object* v_____do__lift_2401_ = stack[18].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2383_, v_methods_2384_, v_____do__lift_2385_, v_____do__lift_2386_, v_x_2387_, v_toPure_2388_, v_inst_2389_, v___f_2390_, v_toBind_2391_, v_setNextMacroScope_2392_, v_inst_2393_, v_inst_2394_, v_inst_2395_, v_toMonadRef_2396_, v_inst_2397_, v_inst_2398_, v_toMonadExceptOf_2399_, v_getNextMacroScope_2400_, v_____do__lift_2401_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2407_ = _args[0];
lean_object* v_methods_2408_ = _args[1];
lean_object* v_____do__lift_2409_ = _args[2];
lean_object* v_____do__lift_2410_ = _args[3];
lean_object* v_x_2411_ = _args[4];
lean_object* v_toPure_2412_ = _args[5];
lean_object* v_inst_2413_ = _args[6];
lean_object* v___f_2414_ = _args[7];
lean_object* v_toBind_2415_ = _args[8];
lean_object* v_setNextMacroScope_2416_ = _args[9];
lean_object* v_inst_2417_ = _args[10];
lean_object* v_inst_2418_ = _args[11];
lean_object* v_inst_2419_ = _args[12];
lean_object* v_toMonadRef_2420_ = _args[13];
lean_object* v_inst_2421_ = _args[14];
lean_object* v_inst_2422_ = _args[15];
lean_object* v_toMonadExceptOf_2423_ = _args[16];
lean_object* v_getNextMacroScope_2424_ = _args[17];
lean_object* v_____do__lift_2425_ = _args[18];
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2407_, v_methods_2408_, v_____do__lift_2409_, v_____do__lift_2410_, v_x_2411_, v_toPure_2412_, v_inst_2413_, v___f_2414_, v_toBind_2415_, v_setNextMacroScope_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_toMonadRef_2420_, v_inst_2421_, v_inst_2422_, v_toMonadExceptOf_2423_, v_getNextMacroScope_2424_, v_____do__lift_2425_);
return v_res_2426_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2427_, lean_object* v_methods_2428_, lean_object* v_____do__lift_2429_, lean_object* v_x_2430_, lean_object* v_toPure_2431_, lean_object* v_inst_2432_, lean_object* v___f_2433_, lean_object* v_toBind_2434_, lean_object* v_setNextMacroScope_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_toMonadRef_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_toMonadExceptOf_2442_, lean_object* v_getNextMacroScope_2443_, lean_object* v_getContext_2444_, lean_object* v_____do__lift_2445_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; 
lean_inc(v_toBind_2434_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2446_, 0, v_inst_2427_);
lean_closure_set(v___f_2446_, 1, v_methods_2428_);
lean_closure_set(v___f_2446_, 2, v_____do__lift_2445_);
lean_closure_set(v___f_2446_, 3, v_____do__lift_2429_);
lean_closure_set(v___f_2446_, 4, v_x_2430_);
lean_closure_set(v___f_2446_, 5, v_toPure_2431_);
lean_closure_set(v___f_2446_, 6, v_inst_2432_);
lean_closure_set(v___f_2446_, 7, v___f_2433_);
lean_closure_set(v___f_2446_, 8, v_toBind_2434_);
lean_closure_set(v___f_2446_, 9, v_setNextMacroScope_2435_);
lean_closure_set(v___f_2446_, 10, v_inst_2436_);
lean_closure_set(v___f_2446_, 11, v_inst_2437_);
lean_closure_set(v___f_2446_, 12, v_inst_2438_);
lean_closure_set(v___f_2446_, 13, v_toMonadRef_2439_);
lean_closure_set(v___f_2446_, 14, v_inst_2440_);
lean_closure_set(v___f_2446_, 15, v_inst_2441_);
lean_closure_set(v___f_2446_, 16, v_toMonadExceptOf_2442_);
lean_closure_set(v___f_2446_, 17, v_getNextMacroScope_2443_);
v___x_2447_ = lean_apply_4(v_toBind_2434_, lean_box(0), lean_box(0), v_getContext_2444_, v___f_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2427_ = stack[0].m_obj;
lean_object* v_methods_2428_ = stack[1].m_obj;
lean_object* v_____do__lift_2429_ = stack[2].m_obj;
lean_object* v_x_2430_ = stack[3].m_obj;
lean_object* v_toPure_2431_ = stack[4].m_obj;
lean_object* v_inst_2432_ = stack[5].m_obj;
lean_object* v___f_2433_ = stack[6].m_obj;
lean_object* v_toBind_2434_ = stack[7].m_obj;
lean_object* v_setNextMacroScope_2435_ = stack[8].m_obj;
lean_object* v_inst_2436_ = stack[9].m_obj;
lean_object* v_inst_2437_ = stack[10].m_obj;
lean_object* v_inst_2438_ = stack[11].m_obj;
lean_object* v_toMonadRef_2439_ = stack[12].m_obj;
lean_object* v_inst_2440_ = stack[13].m_obj;
lean_object* v_inst_2441_ = stack[14].m_obj;
lean_object* v_toMonadExceptOf_2442_ = stack[15].m_obj;
lean_object* v_getNextMacroScope_2443_ = stack[16].m_obj;
lean_object* v_getContext_2444_ = stack[17].m_obj;
lean_object* v_____do__lift_2445_ = stack[18].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2427_, v_methods_2428_, v_____do__lift_2429_, v_x_2430_, v_toPure_2431_, v_inst_2432_, v___f_2433_, v_toBind_2434_, v_setNextMacroScope_2435_, v_inst_2436_, v_inst_2437_, v_inst_2438_, v_toMonadRef_2439_, v_inst_2440_, v_inst_2441_, v_toMonadExceptOf_2442_, v_getNextMacroScope_2443_, v_getContext_2444_, v_____do__lift_2445_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2449_ = _args[0];
lean_object* v_methods_2450_ = _args[1];
lean_object* v_____do__lift_2451_ = _args[2];
lean_object* v_x_2452_ = _args[3];
lean_object* v_toPure_2453_ = _args[4];
lean_object* v_inst_2454_ = _args[5];
lean_object* v___f_2455_ = _args[6];
lean_object* v_toBind_2456_ = _args[7];
lean_object* v_setNextMacroScope_2457_ = _args[8];
lean_object* v_inst_2458_ = _args[9];
lean_object* v_inst_2459_ = _args[10];
lean_object* v_inst_2460_ = _args[11];
lean_object* v_toMonadRef_2461_ = _args[12];
lean_object* v_inst_2462_ = _args[13];
lean_object* v_inst_2463_ = _args[14];
lean_object* v_toMonadExceptOf_2464_ = _args[15];
lean_object* v_getNextMacroScope_2465_ = _args[16];
lean_object* v_getContext_2466_ = _args[17];
lean_object* v_____do__lift_2467_ = _args[18];
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2449_, v_methods_2450_, v_____do__lift_2451_, v_x_2452_, v_toPure_2453_, v_inst_2454_, v___f_2455_, v_toBind_2456_, v_setNextMacroScope_2457_, v_inst_2458_, v_inst_2459_, v_inst_2460_, v_toMonadRef_2461_, v_inst_2462_, v_inst_2463_, v_toMonadExceptOf_2464_, v_getNextMacroScope_2465_, v_getContext_2466_, v_____do__lift_2467_);
return v_res_2468_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2469_, lean_object* v_inst_2470_, lean_object* v_methods_2471_, lean_object* v_x_2472_, lean_object* v_toPure_2473_, lean_object* v_inst_2474_, lean_object* v___f_2475_, lean_object* v_toBind_2476_, lean_object* v_setNextMacroScope_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_toMonadRef_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_toMonadExceptOf_2484_, lean_object* v_getNextMacroScope_2485_, lean_object* v_____do__lift_2486_){
_start:
{
lean_object* v_getCurrMacroScope_2487_; lean_object* v_getContext_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; 
v_getCurrMacroScope_2487_ = lean_ctor_get(v_toMonadQuotation_2469_, 1);
lean_inc(v_getCurrMacroScope_2487_);
v_getContext_2488_ = lean_ctor_get(v_toMonadQuotation_2469_, 2);
lean_inc(v_getContext_2488_);
lean_dec_ref(v_toMonadQuotation_2469_);
lean_inc(v_toBind_2476_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2489_, 0, v_inst_2470_);
lean_closure_set(v___f_2489_, 1, v_methods_2471_);
lean_closure_set(v___f_2489_, 2, v_____do__lift_2486_);
lean_closure_set(v___f_2489_, 3, v_x_2472_);
lean_closure_set(v___f_2489_, 4, v_toPure_2473_);
lean_closure_set(v___f_2489_, 5, v_inst_2474_);
lean_closure_set(v___f_2489_, 6, v___f_2475_);
lean_closure_set(v___f_2489_, 7, v_toBind_2476_);
lean_closure_set(v___f_2489_, 8, v_setNextMacroScope_2477_);
lean_closure_set(v___f_2489_, 9, v_inst_2478_);
lean_closure_set(v___f_2489_, 10, v_inst_2479_);
lean_closure_set(v___f_2489_, 11, v_inst_2480_);
lean_closure_set(v___f_2489_, 12, v_toMonadRef_2481_);
lean_closure_set(v___f_2489_, 13, v_inst_2482_);
lean_closure_set(v___f_2489_, 14, v_inst_2483_);
lean_closure_set(v___f_2489_, 15, v_toMonadExceptOf_2484_);
lean_closure_set(v___f_2489_, 16, v_getNextMacroScope_2485_);
lean_closure_set(v___f_2489_, 17, v_getContext_2488_);
v___x_2490_ = lean_apply_4(v_toBind_2476_, lean_box(0), lean_box(0), v_getCurrMacroScope_2487_, v___f_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadQuotation_2469_ = stack[0].m_obj;
lean_object* v_inst_2470_ = stack[1].m_obj;
lean_object* v_methods_2471_ = stack[2].m_obj;
lean_object* v_x_2472_ = stack[3].m_obj;
lean_object* v_toPure_2473_ = stack[4].m_obj;
lean_object* v_inst_2474_ = stack[5].m_obj;
lean_object* v___f_2475_ = stack[6].m_obj;
lean_object* v_toBind_2476_ = stack[7].m_obj;
lean_object* v_setNextMacroScope_2477_ = stack[8].m_obj;
lean_object* v_inst_2478_ = stack[9].m_obj;
lean_object* v_inst_2479_ = stack[10].m_obj;
lean_object* v_inst_2480_ = stack[11].m_obj;
lean_object* v_toMonadRef_2481_ = stack[12].m_obj;
lean_object* v_inst_2482_ = stack[13].m_obj;
lean_object* v_inst_2483_ = stack[14].m_obj;
lean_object* v_toMonadExceptOf_2484_ = stack[15].m_obj;
lean_object* v_getNextMacroScope_2485_ = stack[16].m_obj;
lean_object* v_____do__lift_2486_ = stack[17].m_obj;
lean_object* v_res_2491_;
v_res_2491_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2469_, v_inst_2470_, v_methods_2471_, v_x_2472_, v_toPure_2473_, v_inst_2474_, v___f_2475_, v_toBind_2476_, v_setNextMacroScope_2477_, v_inst_2478_, v_inst_2479_, v_inst_2480_, v_toMonadRef_2481_, v_inst_2482_, v_inst_2483_, v_toMonadExceptOf_2484_, v_getNextMacroScope_2485_, v_____do__lift_2486_);
stack->m_obj
 = v_res_2491_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2492_ = _args[0];
lean_object* v_inst_2493_ = _args[1];
lean_object* v_methods_2494_ = _args[2];
lean_object* v_x_2495_ = _args[3];
lean_object* v_toPure_2496_ = _args[4];
lean_object* v_inst_2497_ = _args[5];
lean_object* v___f_2498_ = _args[6];
lean_object* v_toBind_2499_ = _args[7];
lean_object* v_setNextMacroScope_2500_ = _args[8];
lean_object* v_inst_2501_ = _args[9];
lean_object* v_inst_2502_ = _args[10];
lean_object* v_inst_2503_ = _args[11];
lean_object* v_toMonadRef_2504_ = _args[12];
lean_object* v_inst_2505_ = _args[13];
lean_object* v_inst_2506_ = _args[14];
lean_object* v_toMonadExceptOf_2507_ = _args[15];
lean_object* v_getNextMacroScope_2508_ = _args[16];
lean_object* v_____do__lift_2509_ = _args[17];
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2492_, v_inst_2493_, v_methods_2494_, v_x_2495_, v_toPure_2496_, v_inst_2497_, v___f_2498_, v_toBind_2499_, v_setNextMacroScope_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_toMonadRef_2504_, v_inst_2505_, v_inst_2506_, v_toMonadExceptOf_2507_, v_getNextMacroScope_2508_, v_____do__lift_2509_);
return v_res_2510_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2511_, lean_object* v_env_2512_, lean_object* v_currNamespace_2513_, lean_object* v_opts_2514_, lean_object* v___x_2515_, lean_object* v___f_2516_, lean_object* v___f_2517_, lean_object* v_toMonadQuotation_2518_, lean_object* v_inst_2519_, lean_object* v_x_2520_, lean_object* v_toPure_2521_, lean_object* v_inst_2522_, lean_object* v___f_2523_, lean_object* v_toBind_2524_, lean_object* v_setNextMacroScope_2525_, lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_toMonadExceptOf_2531_, lean_object* v_getNextMacroScope_2532_, lean_object* v_openDecls_2533_){
_start:
{
lean_object* v_getRef_2534_; lean_object* v___f_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v_methods_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; 
v_getRef_2534_ = lean_ctor_get(v_toMonadRef_2511_, 0);
lean_inc(v_getRef_2534_);
lean_inc(v_openDecls_2533_);
lean_inc_n(v_currNamespace_2513_, 2);
lean_inc_ref(v_env_2512_);
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2535_, 0, v_env_2512_);
lean_closure_set(v___f_2535_, 1, v_currNamespace_2513_);
lean_closure_set(v___f_2535_, 2, v_openDecls_2533_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2536_, 0, v_env_2512_);
lean_closure_set(v___f_2536_, 1, v_opts_2514_);
lean_closure_set(v___f_2536_, 2, v_currNamespace_2513_);
lean_closure_set(v___f_2536_, 3, v_openDecls_2533_);
v___x_2537_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2537_, 0, lean_box(0));
lean_closure_set(v___x_2537_, 1, lean_box(0));
lean_closure_set(v___x_2537_, 2, v___x_2515_);
lean_closure_set(v___x_2537_, 3, lean_box(0));
lean_closure_set(v___x_2537_, 4, v_currNamespace_2513_);
v_methods_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2538_, 0, v___f_2516_);
lean_ctor_set(v_methods_2538_, 1, v___x_2537_);
lean_ctor_set(v_methods_2538_, 2, v___f_2517_);
lean_ctor_set(v_methods_2538_, 3, v___f_2535_);
lean_ctor_set(v_methods_2538_, 4, v___f_2536_);
lean_inc(v_toBind_2524_);
v___f_2539_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2539_, 0, v_toMonadQuotation_2518_);
lean_closure_set(v___f_2539_, 1, v_inst_2519_);
lean_closure_set(v___f_2539_, 2, v_methods_2538_);
lean_closure_set(v___f_2539_, 3, v_x_2520_);
lean_closure_set(v___f_2539_, 4, v_toPure_2521_);
lean_closure_set(v___f_2539_, 5, v_inst_2522_);
lean_closure_set(v___f_2539_, 6, v___f_2523_);
lean_closure_set(v___f_2539_, 7, v_toBind_2524_);
lean_closure_set(v___f_2539_, 8, v_setNextMacroScope_2525_);
lean_closure_set(v___f_2539_, 9, v_inst_2526_);
lean_closure_set(v___f_2539_, 10, v_inst_2527_);
lean_closure_set(v___f_2539_, 11, v_inst_2528_);
lean_closure_set(v___f_2539_, 12, v_toMonadRef_2511_);
lean_closure_set(v___f_2539_, 13, v_inst_2529_);
lean_closure_set(v___f_2539_, 14, v_inst_2530_);
lean_closure_set(v___f_2539_, 15, v_toMonadExceptOf_2531_);
lean_closure_set(v___f_2539_, 16, v_getNextMacroScope_2532_);
v___x_2540_ = lean_apply_4(v_toBind_2524_, lean_box(0), lean_box(0), v_getRef_2534_, v___f_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadRef_2511_ = stack[0].m_obj;
lean_object* v_env_2512_ = stack[1].m_obj;
lean_object* v_currNamespace_2513_ = stack[2].m_obj;
lean_object* v_opts_2514_ = stack[3].m_obj;
lean_object* v___x_2515_ = stack[4].m_obj;
lean_object* v___f_2516_ = stack[5].m_obj;
lean_object* v___f_2517_ = stack[6].m_obj;
lean_object* v_toMonadQuotation_2518_ = stack[7].m_obj;
lean_object* v_inst_2519_ = stack[8].m_obj;
lean_object* v_x_2520_ = stack[9].m_obj;
lean_object* v_toPure_2521_ = stack[10].m_obj;
lean_object* v_inst_2522_ = stack[11].m_obj;
lean_object* v___f_2523_ = stack[12].m_obj;
lean_object* v_toBind_2524_ = stack[13].m_obj;
lean_object* v_setNextMacroScope_2525_ = stack[14].m_obj;
lean_object* v_inst_2526_ = stack[15].m_obj;
lean_object* v_inst_2527_ = stack[16].m_obj;
lean_object* v_inst_2528_ = stack[17].m_obj;
lean_object* v_inst_2529_ = stack[18].m_obj;
lean_object* v_inst_2530_ = stack[19].m_obj;
lean_object* v_toMonadExceptOf_2531_ = stack[20].m_obj;
lean_object* v_getNextMacroScope_2532_ = stack[21].m_obj;
lean_object* v_openDecls_2533_ = stack[22].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2511_, v_env_2512_, v_currNamespace_2513_, v_opts_2514_, v___x_2515_, v___f_2516_, v___f_2517_, v_toMonadQuotation_2518_, v_inst_2519_, v_x_2520_, v_toPure_2521_, v_inst_2522_, v___f_2523_, v_toBind_2524_, v_setNextMacroScope_2525_, v_inst_2526_, v_inst_2527_, v_inst_2528_, v_inst_2529_, v_inst_2530_, v_toMonadExceptOf_2531_, v_getNextMacroScope_2532_, v_openDecls_2533_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2542_ = _args[0];
lean_object* v_env_2543_ = _args[1];
lean_object* v_currNamespace_2544_ = _args[2];
lean_object* v_opts_2545_ = _args[3];
lean_object* v___x_2546_ = _args[4];
lean_object* v___f_2547_ = _args[5];
lean_object* v___f_2548_ = _args[6];
lean_object* v_toMonadQuotation_2549_ = _args[7];
lean_object* v_inst_2550_ = _args[8];
lean_object* v_x_2551_ = _args[9];
lean_object* v_toPure_2552_ = _args[10];
lean_object* v_inst_2553_ = _args[11];
lean_object* v___f_2554_ = _args[12];
lean_object* v_toBind_2555_ = _args[13];
lean_object* v_setNextMacroScope_2556_ = _args[14];
lean_object* v_inst_2557_ = _args[15];
lean_object* v_inst_2558_ = _args[16];
lean_object* v_inst_2559_ = _args[17];
lean_object* v_inst_2560_ = _args[18];
lean_object* v_inst_2561_ = _args[19];
lean_object* v_toMonadExceptOf_2562_ = _args[20];
lean_object* v_getNextMacroScope_2563_ = _args[21];
lean_object* v_openDecls_2564_ = _args[22];
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2542_, v_env_2543_, v_currNamespace_2544_, v_opts_2545_, v___x_2546_, v___f_2547_, v___f_2548_, v_toMonadQuotation_2549_, v_inst_2550_, v_x_2551_, v_toPure_2552_, v_inst_2553_, v___f_2554_, v_toBind_2555_, v_setNextMacroScope_2556_, v_inst_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_toMonadExceptOf_2562_, v_getNextMacroScope_2563_, v_openDecls_2564_);
return v_res_2565_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2566_, lean_object* v_env_2567_, lean_object* v_opts_2568_, lean_object* v___x_2569_, lean_object* v___f_2570_, lean_object* v___f_2571_, lean_object* v_toMonadQuotation_2572_, lean_object* v_inst_2573_, lean_object* v_x_2574_, lean_object* v_toPure_2575_, lean_object* v_inst_2576_, lean_object* v___f_2577_, lean_object* v_toBind_2578_, lean_object* v_setNextMacroScope_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_toMonadExceptOf_2585_, lean_object* v_getNextMacroScope_2586_, lean_object* v_getOpenDecls_2587_, lean_object* v_currNamespace_2588_){
_start:
{
lean_object* v___f_2589_; lean_object* v___x_2590_; 
lean_inc(v_toBind_2578_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2589_, 0, v_toMonadRef_2566_);
lean_closure_set(v___f_2589_, 1, v_env_2567_);
lean_closure_set(v___f_2589_, 2, v_currNamespace_2588_);
lean_closure_set(v___f_2589_, 3, v_opts_2568_);
lean_closure_set(v___f_2589_, 4, v___x_2569_);
lean_closure_set(v___f_2589_, 5, v___f_2570_);
lean_closure_set(v___f_2589_, 6, v___f_2571_);
lean_closure_set(v___f_2589_, 7, v_toMonadQuotation_2572_);
lean_closure_set(v___f_2589_, 8, v_inst_2573_);
lean_closure_set(v___f_2589_, 9, v_x_2574_);
lean_closure_set(v___f_2589_, 10, v_toPure_2575_);
lean_closure_set(v___f_2589_, 11, v_inst_2576_);
lean_closure_set(v___f_2589_, 12, v___f_2577_);
lean_closure_set(v___f_2589_, 13, v_toBind_2578_);
lean_closure_set(v___f_2589_, 14, v_setNextMacroScope_2579_);
lean_closure_set(v___f_2589_, 15, v_inst_2580_);
lean_closure_set(v___f_2589_, 16, v_inst_2581_);
lean_closure_set(v___f_2589_, 17, v_inst_2582_);
lean_closure_set(v___f_2589_, 18, v_inst_2583_);
lean_closure_set(v___f_2589_, 19, v_inst_2584_);
lean_closure_set(v___f_2589_, 20, v_toMonadExceptOf_2585_);
lean_closure_set(v___f_2589_, 21, v_getNextMacroScope_2586_);
v___x_2590_ = lean_apply_4(v_toBind_2578_, lean_box(0), lean_box(0), v_getOpenDecls_2587_, v___f_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadRef_2566_ = stack[0].m_obj;
lean_object* v_env_2567_ = stack[1].m_obj;
lean_object* v_opts_2568_ = stack[2].m_obj;
lean_object* v___x_2569_ = stack[3].m_obj;
lean_object* v___f_2570_ = stack[4].m_obj;
lean_object* v___f_2571_ = stack[5].m_obj;
lean_object* v_toMonadQuotation_2572_ = stack[6].m_obj;
lean_object* v_inst_2573_ = stack[7].m_obj;
lean_object* v_x_2574_ = stack[8].m_obj;
lean_object* v_toPure_2575_ = stack[9].m_obj;
lean_object* v_inst_2576_ = stack[10].m_obj;
lean_object* v___f_2577_ = stack[11].m_obj;
lean_object* v_toBind_2578_ = stack[12].m_obj;
lean_object* v_setNextMacroScope_2579_ = stack[13].m_obj;
lean_object* v_inst_2580_ = stack[14].m_obj;
lean_object* v_inst_2581_ = stack[15].m_obj;
lean_object* v_inst_2582_ = stack[16].m_obj;
lean_object* v_inst_2583_ = stack[17].m_obj;
lean_object* v_inst_2584_ = stack[18].m_obj;
lean_object* v_toMonadExceptOf_2585_ = stack[19].m_obj;
lean_object* v_getNextMacroScope_2586_ = stack[20].m_obj;
lean_object* v_getOpenDecls_2587_ = stack[21].m_obj;
lean_object* v_currNamespace_2588_ = stack[22].m_obj;
lean_object* v_res_2591_;
v_res_2591_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2566_, v_env_2567_, v_opts_2568_, v___x_2569_, v___f_2570_, v___f_2571_, v_toMonadQuotation_2572_, v_inst_2573_, v_x_2574_, v_toPure_2575_, v_inst_2576_, v___f_2577_, v_toBind_2578_, v_setNextMacroScope_2579_, v_inst_2580_, v_inst_2581_, v_inst_2582_, v_inst_2583_, v_inst_2584_, v_toMonadExceptOf_2585_, v_getNextMacroScope_2586_, v_getOpenDecls_2587_, v_currNamespace_2588_);
stack->m_obj
 = v_res_2591_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2592_ = _args[0];
lean_object* v_env_2593_ = _args[1];
lean_object* v_opts_2594_ = _args[2];
lean_object* v___x_2595_ = _args[3];
lean_object* v___f_2596_ = _args[4];
lean_object* v___f_2597_ = _args[5];
lean_object* v_toMonadQuotation_2598_ = _args[6];
lean_object* v_inst_2599_ = _args[7];
lean_object* v_x_2600_ = _args[8];
lean_object* v_toPure_2601_ = _args[9];
lean_object* v_inst_2602_ = _args[10];
lean_object* v___f_2603_ = _args[11];
lean_object* v_toBind_2604_ = _args[12];
lean_object* v_setNextMacroScope_2605_ = _args[13];
lean_object* v_inst_2606_ = _args[14];
lean_object* v_inst_2607_ = _args[15];
lean_object* v_inst_2608_ = _args[16];
lean_object* v_inst_2609_ = _args[17];
lean_object* v_inst_2610_ = _args[18];
lean_object* v_toMonadExceptOf_2611_ = _args[19];
lean_object* v_getNextMacroScope_2612_ = _args[20];
lean_object* v_getOpenDecls_2613_ = _args[21];
lean_object* v_currNamespace_2614_ = _args[22];
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2592_, v_env_2593_, v_opts_2594_, v___x_2595_, v___f_2596_, v___f_2597_, v_toMonadQuotation_2598_, v_inst_2599_, v_x_2600_, v_toPure_2601_, v_inst_2602_, v___f_2603_, v_toBind_2604_, v_setNextMacroScope_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v_inst_2609_, v_inst_2610_, v_toMonadExceptOf_2611_, v_getNextMacroScope_2612_, v_getOpenDecls_2613_, v_currNamespace_2614_);
return v_res_2615_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2616_, lean_object* v_toMonadRef_2617_, lean_object* v_env_2618_, lean_object* v___x_2619_, lean_object* v___f_2620_, lean_object* v___f_2621_, lean_object* v_toMonadQuotation_2622_, lean_object* v_inst_2623_, lean_object* v_x_2624_, lean_object* v_toPure_2625_, lean_object* v_inst_2626_, lean_object* v___f_2627_, lean_object* v_toBind_2628_, lean_object* v_setNextMacroScope_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_toMonadExceptOf_2635_, lean_object* v_getNextMacroScope_2636_, lean_object* v_opts_2637_){
_start:
{
lean_object* v_getCurrNamespace_2638_; lean_object* v_getOpenDecls_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; 
v_getCurrNamespace_2638_ = lean_ctor_get(v_inst_2616_, 0);
lean_inc(v_getCurrNamespace_2638_);
v_getOpenDecls_2639_ = lean_ctor_get(v_inst_2616_, 1);
lean_inc(v_getOpenDecls_2639_);
lean_dec_ref(v_inst_2616_);
lean_inc(v_toBind_2628_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2640_, 0, v_toMonadRef_2617_);
lean_closure_set(v___f_2640_, 1, v_env_2618_);
lean_closure_set(v___f_2640_, 2, v_opts_2637_);
lean_closure_set(v___f_2640_, 3, v___x_2619_);
lean_closure_set(v___f_2640_, 4, v___f_2620_);
lean_closure_set(v___f_2640_, 5, v___f_2621_);
lean_closure_set(v___f_2640_, 6, v_toMonadQuotation_2622_);
lean_closure_set(v___f_2640_, 7, v_inst_2623_);
lean_closure_set(v___f_2640_, 8, v_x_2624_);
lean_closure_set(v___f_2640_, 9, v_toPure_2625_);
lean_closure_set(v___f_2640_, 10, v_inst_2626_);
lean_closure_set(v___f_2640_, 11, v___f_2627_);
lean_closure_set(v___f_2640_, 12, v_toBind_2628_);
lean_closure_set(v___f_2640_, 13, v_setNextMacroScope_2629_);
lean_closure_set(v___f_2640_, 14, v_inst_2630_);
lean_closure_set(v___f_2640_, 15, v_inst_2631_);
lean_closure_set(v___f_2640_, 16, v_inst_2632_);
lean_closure_set(v___f_2640_, 17, v_inst_2633_);
lean_closure_set(v___f_2640_, 18, v_inst_2634_);
lean_closure_set(v___f_2640_, 19, v_toMonadExceptOf_2635_);
lean_closure_set(v___f_2640_, 20, v_getNextMacroScope_2636_);
lean_closure_set(v___f_2640_, 21, v_getOpenDecls_2639_);
v___x_2641_ = lean_apply_4(v_toBind_2628_, lean_box(0), lean_box(0), v_getCurrNamespace_2638_, v___f_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2616_ = stack[0].m_obj;
lean_object* v_toMonadRef_2617_ = stack[1].m_obj;
lean_object* v_env_2618_ = stack[2].m_obj;
lean_object* v___x_2619_ = stack[3].m_obj;
lean_object* v___f_2620_ = stack[4].m_obj;
lean_object* v___f_2621_ = stack[5].m_obj;
lean_object* v_toMonadQuotation_2622_ = stack[6].m_obj;
lean_object* v_inst_2623_ = stack[7].m_obj;
lean_object* v_x_2624_ = stack[8].m_obj;
lean_object* v_toPure_2625_ = stack[9].m_obj;
lean_object* v_inst_2626_ = stack[10].m_obj;
lean_object* v___f_2627_ = stack[11].m_obj;
lean_object* v_toBind_2628_ = stack[12].m_obj;
lean_object* v_setNextMacroScope_2629_ = stack[13].m_obj;
lean_object* v_inst_2630_ = stack[14].m_obj;
lean_object* v_inst_2631_ = stack[15].m_obj;
lean_object* v_inst_2632_ = stack[16].m_obj;
lean_object* v_inst_2633_ = stack[17].m_obj;
lean_object* v_inst_2634_ = stack[18].m_obj;
lean_object* v_toMonadExceptOf_2635_ = stack[19].m_obj;
lean_object* v_getNextMacroScope_2636_ = stack[20].m_obj;
lean_object* v_opts_2637_ = stack[21].m_obj;
lean_object* v_res_2642_;
v_res_2642_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2616_, v_toMonadRef_2617_, v_env_2618_, v___x_2619_, v___f_2620_, v___f_2621_, v_toMonadQuotation_2622_, v_inst_2623_, v_x_2624_, v_toPure_2625_, v_inst_2626_, v___f_2627_, v_toBind_2628_, v_setNextMacroScope_2629_, v_inst_2630_, v_inst_2631_, v_inst_2632_, v_inst_2633_, v_inst_2634_, v_toMonadExceptOf_2635_, v_getNextMacroScope_2636_, v_opts_2637_);
stack->m_obj
 = v_res_2642_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2643_ = _args[0];
lean_object* v_toMonadRef_2644_ = _args[1];
lean_object* v_env_2645_ = _args[2];
lean_object* v___x_2646_ = _args[3];
lean_object* v___f_2647_ = _args[4];
lean_object* v___f_2648_ = _args[5];
lean_object* v_toMonadQuotation_2649_ = _args[6];
lean_object* v_inst_2650_ = _args[7];
lean_object* v_x_2651_ = _args[8];
lean_object* v_toPure_2652_ = _args[9];
lean_object* v_inst_2653_ = _args[10];
lean_object* v___f_2654_ = _args[11];
lean_object* v_toBind_2655_ = _args[12];
lean_object* v_setNextMacroScope_2656_ = _args[13];
lean_object* v_inst_2657_ = _args[14];
lean_object* v_inst_2658_ = _args[15];
lean_object* v_inst_2659_ = _args[16];
lean_object* v_inst_2660_ = _args[17];
lean_object* v_inst_2661_ = _args[18];
lean_object* v_toMonadExceptOf_2662_ = _args[19];
lean_object* v_getNextMacroScope_2663_ = _args[20];
lean_object* v_opts_2664_ = _args[21];
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2643_, v_toMonadRef_2644_, v_env_2645_, v___x_2646_, v___f_2647_, v___f_2648_, v_toMonadQuotation_2649_, v_inst_2650_, v_x_2651_, v_toPure_2652_, v_inst_2653_, v___f_2654_, v_toBind_2655_, v_setNextMacroScope_2656_, v_inst_2657_, v_inst_2658_, v_inst_2659_, v_inst_2660_, v_inst_2661_, v_toMonadExceptOf_2662_, v_getNextMacroScope_2663_, v_opts_2664_);
return v_res_2665_;
}
}
lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v_inst_2666_, lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v_inst_2669_, lean_object* v_toMonadRef_2670_, lean_object* v___x_2671_, lean_object* v_toMonadQuotation_2672_, lean_object* v_inst_2673_, lean_object* v_x_2674_, lean_object* v_toPure_2675_, lean_object* v_inst_2676_, lean_object* v___f_2677_, lean_object* v_toBind_2678_, lean_object* v_setNextMacroScope_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_toMonadExceptOf_2684_, lean_object* v_getNextMacroScope_2685_, lean_object* v_env_2686_){
_start:
{
lean_object* v_getOptions_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; 
v_getOptions_2687_ = lean_ctor_get(v_inst_2666_, 0);
lean_inc(v_getOptions_2687_);
lean_inc_ref_n(v_env_2686_, 2);
v___f_2688_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2688_, 0, v_env_2686_);
lean_closure_set(v___f_2688_, 1, v___x_2667_);
lean_closure_set(v___f_2688_, 2, v___x_2668_);
v___f_2689_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2689_, 0, v_env_2686_);
lean_inc(v_toBind_2678_);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2690_, 0, v_inst_2669_);
lean_closure_set(v___f_2690_, 1, v_toMonadRef_2670_);
lean_closure_set(v___f_2690_, 2, v_env_2686_);
lean_closure_set(v___f_2690_, 3, v___x_2671_);
lean_closure_set(v___f_2690_, 4, v___f_2688_);
lean_closure_set(v___f_2690_, 5, v___f_2689_);
lean_closure_set(v___f_2690_, 6, v_toMonadQuotation_2672_);
lean_closure_set(v___f_2690_, 7, v_inst_2673_);
lean_closure_set(v___f_2690_, 8, v_x_2674_);
lean_closure_set(v___f_2690_, 9, v_toPure_2675_);
lean_closure_set(v___f_2690_, 10, v_inst_2676_);
lean_closure_set(v___f_2690_, 11, v___f_2677_);
lean_closure_set(v___f_2690_, 12, v_toBind_2678_);
lean_closure_set(v___f_2690_, 13, v_setNextMacroScope_2679_);
lean_closure_set(v___f_2690_, 14, v_inst_2680_);
lean_closure_set(v___f_2690_, 15, v_inst_2681_);
lean_closure_set(v___f_2690_, 16, v_inst_2666_);
lean_closure_set(v___f_2690_, 17, v_inst_2682_);
lean_closure_set(v___f_2690_, 18, v_inst_2683_);
lean_closure_set(v___f_2690_, 19, v_toMonadExceptOf_2684_);
lean_closure_set(v___f_2690_, 20, v_getNextMacroScope_2685_);
v___x_2691_ = lean_apply_4(v_toBind_2678_, lean_box(0), lean_box(0), v_getOptions_2687_, v___f_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___redArg___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2666_ = stack[0].m_obj;
lean_object* v___x_2667_ = stack[1].m_obj;
lean_object* v___x_2668_ = stack[2].m_obj;
lean_object* v_inst_2669_ = stack[3].m_obj;
lean_object* v_toMonadRef_2670_ = stack[4].m_obj;
lean_object* v___x_2671_ = stack[5].m_obj;
lean_object* v_toMonadQuotation_2672_ = stack[6].m_obj;
lean_object* v_inst_2673_ = stack[7].m_obj;
lean_object* v_x_2674_ = stack[8].m_obj;
lean_object* v_toPure_2675_ = stack[9].m_obj;
lean_object* v_inst_2676_ = stack[10].m_obj;
lean_object* v___f_2677_ = stack[11].m_obj;
lean_object* v_toBind_2678_ = stack[12].m_obj;
lean_object* v_setNextMacroScope_2679_ = stack[13].m_obj;
lean_object* v_inst_2680_ = stack[14].m_obj;
lean_object* v_inst_2681_ = stack[15].m_obj;
lean_object* v_inst_2682_ = stack[16].m_obj;
lean_object* v_inst_2683_ = stack[17].m_obj;
lean_object* v_toMonadExceptOf_2684_ = stack[18].m_obj;
lean_object* v_getNextMacroScope_2685_ = stack[19].m_obj;
lean_object* v_env_2686_ = stack[20].m_obj;
lean_object* v_res_2692_;
v_res_2692_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v_inst_2666_, v___x_2667_, v___x_2668_, v_inst_2669_, v_toMonadRef_2670_, v___x_2671_, v_toMonadQuotation_2672_, v_inst_2673_, v_x_2674_, v_toPure_2675_, v_inst_2676_, v___f_2677_, v_toBind_2678_, v_setNextMacroScope_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_toMonadExceptOf_2684_, v_getNextMacroScope_2685_, v_env_2686_);
stack->m_obj
 = v_res_2692_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_inst_2693_ = _args[0];
lean_object* v___x_2694_ = _args[1];
lean_object* v___x_2695_ = _args[2];
lean_object* v_inst_2696_ = _args[3];
lean_object* v_toMonadRef_2697_ = _args[4];
lean_object* v___x_2698_ = _args[5];
lean_object* v_toMonadQuotation_2699_ = _args[6];
lean_object* v_inst_2700_ = _args[7];
lean_object* v_x_2701_ = _args[8];
lean_object* v_toPure_2702_ = _args[9];
lean_object* v_inst_2703_ = _args[10];
lean_object* v___f_2704_ = _args[11];
lean_object* v_toBind_2705_ = _args[12];
lean_object* v_setNextMacroScope_2706_ = _args[13];
lean_object* v_inst_2707_ = _args[14];
lean_object* v_inst_2708_ = _args[15];
lean_object* v_inst_2709_ = _args[16];
lean_object* v_inst_2710_ = _args[17];
lean_object* v_toMonadExceptOf_2711_ = _args[18];
lean_object* v_getNextMacroScope_2712_ = _args[19];
lean_object* v_env_2713_ = _args[20];
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v_inst_2693_, v___x_2694_, v___x_2695_, v_inst_2696_, v_toMonadRef_2697_, v___x_2698_, v_toMonadQuotation_2699_, v_inst_2700_, v_x_2701_, v_toPure_2702_, v_inst_2703_, v___f_2704_, v_toBind_2705_, v_setNextMacroScope_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_toMonadExceptOf_2711_, v_getNextMacroScope_2712_, v_env_2713_);
return v_res_2714_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_EStateM_nonBacktrackable___redArg();
return v___x_2734_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2736_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2735_);
return v___x_2736_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___f_2738_; 
v___x_2737_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2738_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2738_, 0, v___x_2737_);
return v___f_2738_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___f_2740_; 
v___x_2739_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2740_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2740_, 0, v___x_2739_);
return v___f_2740_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; 
v___f_2741_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2742_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___f_2742_);
lean_ctor_set(v___x_2743_, 1, v___f_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v_toApplicative_2758_; lean_object* v_toBind_2759_; lean_object* v_getEnv_2760_; lean_object* v_toMonadExceptOf_2761_; lean_object* v_toMonadRef_2762_; lean_object* v_toMonadQuotation_2763_; lean_object* v_getNextMacroScope_2764_; lean_object* v_setNextMacroScope_2765_; lean_object* v_toPure_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; 
v___x_2756_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2757_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2758_ = lean_ctor_get(v_inst_2746_, 0);
v_toBind_2759_ = lean_ctor_get(v_inst_2746_, 1);
lean_inc_n(v_toBind_2759_, 3);
v_getEnv_2760_ = lean_ctor_get(v_inst_2748_, 0);
lean_inc(v_getEnv_2760_);
v_toMonadExceptOf_2761_ = lean_ctor_get(v_inst_2750_, 0);
lean_inc_ref(v_toMonadExceptOf_2761_);
v_toMonadRef_2762_ = lean_ctor_get(v_inst_2750_, 1);
lean_inc_ref_n(v_toMonadRef_2762_, 2);
v_toMonadQuotation_2763_ = lean_ctor_get(v_inst_2747_, 0);
lean_inc_ref(v_toMonadQuotation_2763_);
v_getNextMacroScope_2764_ = lean_ctor_get(v_inst_2747_, 1);
lean_inc(v_getNextMacroScope_2764_);
v_setNextMacroScope_2765_ = lean_ctor_get(v_inst_2747_, 2);
lean_inc(v_setNextMacroScope_2765_);
lean_dec_ref(v_inst_2747_);
v_toPure_2766_ = lean_ctor_get(v_toApplicative_2758_, 1);
lean_inc_n(v_toPure_2766_, 2);
v___x_2767_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2754_);
lean_inc_ref(v_inst_2746_);
lean_inc_ref(v_inst_2753_);
lean_inc_ref(v_inst_2752_);
v___f_2768_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2768_, 0, v_inst_2752_);
lean_closure_set(v___f_2768_, 1, v_inst_2753_);
lean_closure_set(v___f_2768_, 2, v_toPure_2766_);
lean_closure_set(v___f_2768_, 3, v_toBind_2759_);
lean_closure_set(v___f_2768_, 4, v_inst_2746_);
lean_closure_set(v___f_2768_, 5, v_toMonadRef_2762_);
lean_closure_set(v___f_2768_, 6, v_inst_2754_);
v___f_2769_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2769_, 0, v_inst_2753_);
lean_closure_set(v___f_2769_, 1, v___x_2757_);
lean_closure_set(v___f_2769_, 2, v___x_2767_);
lean_closure_set(v___f_2769_, 3, v_inst_2751_);
lean_closure_set(v___f_2769_, 4, v_toMonadRef_2762_);
lean_closure_set(v___f_2769_, 5, v___x_2756_);
lean_closure_set(v___f_2769_, 6, v_toMonadQuotation_2763_);
lean_closure_set(v___f_2769_, 7, v_inst_2749_);
lean_closure_set(v___f_2769_, 8, v_x_2755_);
lean_closure_set(v___f_2769_, 9, v_toPure_2766_);
lean_closure_set(v___f_2769_, 10, v_inst_2746_);
lean_closure_set(v___f_2769_, 11, v___f_2768_);
lean_closure_set(v___f_2769_, 12, v_toBind_2759_);
lean_closure_set(v___f_2769_, 13, v_setNextMacroScope_2765_);
lean_closure_set(v___f_2769_, 14, v_inst_2748_);
lean_closure_set(v___f_2769_, 15, v_inst_2752_);
lean_closure_set(v___f_2769_, 16, v_inst_2754_);
lean_closure_set(v___f_2769_, 17, v_inst_2750_);
lean_closure_set(v___f_2769_, 18, v_toMonadExceptOf_2761_);
lean_closure_set(v___f_2769_, 19, v_getNextMacroScope_2764_);
v___x_2770_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v_getEnv_2760_, v___f_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2771_, lean_object* v_00_u03b1_2772_, lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_inst_2782_, lean_object* v_x_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2773_, v_inst_2774_, v_inst_2775_, v_inst_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_, v_inst_2780_, v_inst_2781_, v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2785_, lean_object* v_00_u03b1_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_inst_2796_, lean_object* v_x_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_liftMacroM(v_m_2785_, v_00_u03b1_2786_, v_inst_2787_, v_inst_2788_, v_inst_2789_, v_inst_2790_, v_inst_2791_, v_inst_2792_, v_inst_2793_, v_inst_2794_, v_inst_2795_, v_inst_2796_, v_x_2797_);
lean_dec(v_inst_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_inst_2807_, lean_object* v_x_2808_, lean_object* v_stx_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_apply_1(v_x_2808_, v_stx_2809_);
v___x_2811_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2799_, v_inst_2800_, v_inst_2801_, v_inst_2802_, v_inst_2803_, v_inst_2804_, v_inst_2805_, v_inst_2806_, v_inst_2807_, v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2812_, lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_inst_2822_, lean_object* v_x_2823_, lean_object* v_stx_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_apply_1(v_x_2823_, v_stx_2824_);
v___x_2826_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2813_, v_inst_2814_, v_inst_2815_, v_inst_2816_, v_inst_2817_, v_inst_2818_, v_inst_2819_, v_inst_2820_, v_inst_2821_, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_x_2838_, lean_object* v_stx_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Elab_adaptMacro(v_m_2827_, v_inst_2828_, v_inst_2829_, v_inst_2830_, v_inst_2831_, v_inst_2832_, v_inst_2833_, v_inst_2834_, v_inst_2835_, v_inst_2836_, v_inst_2837_, v_x_2838_, v_stx_2839_);
lean_dec(v_inst_2837_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2841_, lean_object* v_currNamespace_2842_, lean_object* v_idx_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_name_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_inc(v_idx_2843_);
lean_inc(v_baseName_2841_);
v_name_2846_ = lean_name_append_index_after(v_baseName_2841_, v_idx_2843_);
lean_inc(v_name_2846_);
lean_inc(v_currNamespace_2842_);
v___x_2847_ = l_Lean_Name_append(v_currNamespace_2842_, v_name_2846_);
v___x_2848_ = l_Lean_Macro_hasDecl(v___x_2847_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; uint8_t v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v___x_2850_ = lean_unbox(v_a_2849_);
if (v___x_2850_ == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_idx_2843_);
lean_dec(v_currNamespace_2842_);
lean_dec(v_baseName_2841_);
v_a_2851_ = lean_ctor_get(v___x_2848_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2859_);
v___x_2853_ = v___x_2848_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2848_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_name_2846_);
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_name_2846_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec(v_name_2846_);
v_a_2860_ = lean_ctor_get(v___x_2848_, 1);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2848_, 2);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v_idx_2843_, v___x_2861_);
lean_dec(v_idx_2843_);
v_idx_2843_ = v___x_2862_;
v_a_2845_ = v_a_2860_;
goto _start;
}
}
else
{
lean_object* v_a_2864_; lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_name_2846_);
lean_dec(v_idx_2843_);
lean_dec(v_currNamespace_2842_);
lean_dec(v_baseName_2841_);
v_a_2864_ = lean_ctor_get(v___x_2848_, 0);
v_a_2865_ = lean_ctor_get(v___x_2848_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2848_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_inc(v_a_2864_);
lean_dec(v___x_2848_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2864_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2873_, lean_object* v_currNamespace_2874_, lean_object* v_idx_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2873_, v_currNamespace_2874_, v_idx_2875_, v_a_2876_, v_a_2877_);
lean_dec_ref(v_a_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Macro_getCurrNamespace(v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_a_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_n(v_a_2883_, 2);
v_a_2884_ = lean_ctor_get(v___x_2882_, 1);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2882_, 2);
lean_inc(v_baseName_2879_);
v___x_2885_ = l_Lean_Name_append(v_a_2883_, v_baseName_2879_);
v___x_2886_ = l_Lean_Macro_hasDecl(v___x_2885_, v_a_2880_, v_a_2884_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; uint8_t v___x_2888_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v___x_2888_ = lean_unbox(v_a_2887_);
if (v___x_2888_ == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_a_2883_);
v_a_2889_ = lean_ctor_get(v___x_2886_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2897_);
v___x_2891_ = v___x_2886_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2886_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v_baseName_2879_);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_baseName_2879_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v___x_2886_, 1);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2886_, 2);
v___x_2899_ = lean_unsigned_to_nat(1u);
v___x_2900_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2879_, v_a_2883_, v___x_2899_, v_a_2880_, v_a_2898_);
return v___x_2900_;
}
}
else
{
lean_object* v_a_2901_; lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2883_);
lean_dec(v_baseName_2879_);
v_a_2901_ = lean_ctor_get(v___x_2886_, 0);
v_a_2902_ = lean_ctor_get(v___x_2886_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2886_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_inc(v_a_2901_);
lean_dec(v___x_2886_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2901_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_dec(v_baseName_2879_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2910_, v_a_2911_, v_a_2912_);
lean_dec_ref(v_a_2911_);
return v_res_2913_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2916_ = l_Lean_stringToMessageData(v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_name_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2923_ = l_Lean_MessageData_ofName(v_name_2921_);
v___x_2924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = l_Lean_logError___redArg(v_inst_2917_, v_inst_2918_, v_inst_2919_, v_inst_2920_, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_ex_2931_){
_start:
{
if (lean_obj_tag(v_ex_2931_) == 0)
{
lean_object* v_ref_2932_; lean_object* v_msg_2933_; lean_object* v___x_2934_; 
lean_dec(v_inst_2930_);
v_ref_2932_ = lean_ctor_get(v_ex_2931_, 0);
lean_inc(v_ref_2932_);
v_msg_2933_ = lean_ctor_get(v_ex_2931_, 1);
lean_inc_ref(v_msg_2933_);
lean_dec_ref_known(v_ex_2931_, 2);
v___x_2934_ = l_Lean_logErrorAt___redArg(v_inst_2926_, v_inst_2927_, v_inst_2928_, v_inst_2929_, v_ref_2932_, v_msg_2933_);
return v___x_2934_;
}
else
{
lean_object* v_toApplicative_2935_; lean_object* v_toBind_2936_; lean_object* v_toPure_2937_; lean_object* v_id_2938_; lean_object* v___f_2939_; uint8_t v___y_2941_; uint8_t v___x_2947_; 
v_toApplicative_2935_ = lean_ctor_get(v_inst_2926_, 0);
v_toBind_2936_ = lean_ctor_get(v_inst_2926_, 1);
lean_inc(v_toBind_2936_);
v_toPure_2937_ = lean_ctor_get(v_toApplicative_2935_, 1);
lean_inc(v_toPure_2937_);
v_id_2938_ = lean_ctor_get(v_ex_2931_, 0);
lean_inc(v_id_2938_);
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2939_, 0, v_inst_2926_);
lean_closure_set(v___f_2939_, 1, v_inst_2927_);
lean_closure_set(v___f_2939_, 2, v_inst_2928_);
lean_closure_set(v___f_2939_, 3, v_inst_2929_);
v___x_2947_ = l_Lean_Elab_isAbortExceptionId(v_id_2938_);
if (v___x_2947_ == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Lean_Exception_isInterrupt(v_ex_2931_);
lean_dec_ref_known(v_ex_2931_, 2);
v___y_2941_ = v___x_2948_;
goto v___jp_2940_;
}
else
{
lean_dec_ref_known(v_ex_2931_, 2);
v___y_2941_ = v___x_2947_;
goto v___jp_2940_;
}
v___jp_2940_:
{
if (v___y_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v_toPure_2937_);
v___x_2942_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2942_, 0, v_id_2938_);
v___x_2943_ = lean_apply_2(v_inst_2930_, lean_box(0), v___x_2942_);
v___x_2944_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v___x_2943_, v___f_2939_);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_dec_ref(v___f_2939_);
lean_dec(v_id_2938_);
lean_dec(v_toBind_2936_);
lean_dec(v_inst_2930_);
v___x_2945_ = lean_box(0);
v___x_2946_ = lean_apply_2(v_toPure_2937_, lean_box(0), v___x_2945_);
return v___x_2946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_ex_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Elab_logException___redArg(v_inst_2950_, v_inst_2951_, v_inst_2952_, v_inst_2953_, v_inst_2954_, v_ex_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_ex_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Elab_logException___redArg(v_inst_2957_, v_inst_2958_, v_inst_2959_, v_inst_2960_, v_inst_2961_, v_ex_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_x_2970_){
_start:
{
lean_object* v_tryCatch_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; 
v_tryCatch_2971_ = lean_ctor_get(v_inst_2966_, 1);
lean_inc(v_tryCatch_2971_);
lean_dec_ref(v_inst_2966_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2972_, 0, v_inst_2964_);
lean_closure_set(v___f_2972_, 1, v_inst_2965_);
lean_closure_set(v___f_2972_, 2, v_inst_2967_);
lean_closure_set(v___f_2972_, 3, v_inst_2968_);
lean_closure_set(v___f_2972_, 4, v_inst_2969_);
v___x_2973_ = lean_apply_3(v_tryCatch_2971_, lean_box(0), v_x_2970_, v___f_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Elab_withLogging___redArg(v_inst_2975_, v_inst_2976_, v_inst_2977_, v_inst_2978_, v_inst_2979_, v_inst_2980_, v_x_2981_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2985_ = l_Lean_stringToMessageData(v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2986_, lean_object* v_ex_2987_, lean_object* v_toPure_2988_, lean_object* v_____do__lift_2989_){
_start:
{
lean_object* v_exPosition_2990_; lean_object* v_line_2991_; lean_object* v_column_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3012_; 
v_exPosition_2990_ = l_Lean_FileMap_toPosition(v_____do__lift_2989_, v_val_2986_);
v_line_2991_ = lean_ctor_get(v_exPosition_2990_, 0);
v_column_2992_ = lean_ctor_get(v_exPosition_2990_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_exPosition_2990_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2994_ = v_exPosition_2990_;
v_isShared_2995_ = v_isSharedCheck_3012_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_column_2992_);
lean_inc(v_line_2991_);
lean_dec(v_exPosition_2990_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3012_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2996_ = l_Nat_reprFast(v_line_2991_);
v___x_2997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = l_Lean_MessageData_ofFormat(v___x_2997_);
v___x_2999_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 7);
lean_ctor_set(v___x_2994_, 1, v___x_2999_);
lean_ctor_set(v___x_2994_, 0, v___x_2998_);
v___x_3001_ = v___x_2994_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3002_ = l_Nat_reprFast(v_column_2992_);
v___x_3003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofFormat(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3001_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_Exception_toMessageData(v_ex_2987_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = lean_apply_2(v_toPure_2988_, lean_box(0), v___x_3009_);
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_3013_, lean_object* v_ex_3014_, lean_object* v_toPure_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_3013_, v_ex_3014_, v_toPure_3015_, v_____do__lift_3016_);
lean_dec(v_val_3013_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_3018_, lean_object* v_toPure_3019_, lean_object* v_toBind_3020_, lean_object* v_toMonadFileMap_3021_, lean_object* v_pos_3022_){
_start:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = l_Lean_Exception_getRef(v_ex_3018_);
v___x_3024_ = 0;
v___x_3025_ = l_Lean_Syntax_getPos_x3f(v___x_3023_, v___x_3024_);
lean_dec(v___x_3023_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_dec(v_toMonadFileMap_3021_);
lean_dec(v_toBind_3020_);
v___x_3026_ = l_Lean_Exception_toMessageData(v_ex_3018_);
v___x_3027_ = lean_apply_2(v_toPure_3019_, lean_box(0), v___x_3026_);
return v___x_3027_;
}
else
{
lean_object* v_val_3028_; uint8_t v_decide_3029_; 
v_val_3028_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___x_3025_, 1);
v_decide_3029_ = lean_nat_dec_eq(v_pos_3022_, v_val_3028_);
if (v_decide_3029_ == 0)
{
lean_object* v___f_3030_; lean_object* v___x_3031_; 
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3030_, 0, v_val_3028_);
lean_closure_set(v___f_3030_, 1, v_ex_3018_);
lean_closure_set(v___f_3030_, 2, v_toPure_3019_);
v___x_3031_ = lean_apply_4(v_toBind_3020_, lean_box(0), lean_box(0), v_toMonadFileMap_3021_, v___f_3030_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v_val_3028_);
lean_dec(v_toMonadFileMap_3021_);
lean_dec(v_toBind_3020_);
v___x_3032_ = l_Lean_Exception_toMessageData(v_ex_3018_);
v___x_3033_ = lean_apply_2(v_toPure_3019_, lean_box(0), v___x_3032_);
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_3034_, lean_object* v_toPure_3035_, lean_object* v_toBind_3036_, lean_object* v_toMonadFileMap_3037_, lean_object* v_pos_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_3034_, v_toPure_3035_, v_toBind_3036_, v_toMonadFileMap_3037_, v_pos_3038_);
lean_dec(v_pos_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_ex_3042_){
_start:
{
lean_object* v_toApplicative_3043_; lean_object* v_toBind_3044_; lean_object* v_toPure_3045_; lean_object* v_toMonadFileMap_3046_; lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; 
v_toApplicative_3043_ = lean_ctor_get(v_inst_3040_, 0);
v_toBind_3044_ = lean_ctor_get(v_inst_3040_, 1);
lean_inc_n(v_toBind_3044_, 2);
v_toPure_3045_ = lean_ctor_get(v_toApplicative_3043_, 1);
lean_inc(v_toPure_3045_);
v_toMonadFileMap_3046_ = lean_ctor_get(v_inst_3041_, 0);
lean_inc(v_toMonadFileMap_3046_);
v___x_3047_ = l_Lean_getRefPos___redArg(v_inst_3040_, v_inst_3041_);
v___f_3048_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3048_, 0, v_ex_3042_);
lean_closure_set(v___f_3048_, 1, v_toPure_3045_);
lean_closure_set(v___f_3048_, 2, v_toBind_3044_);
lean_closure_set(v___f_3048_, 3, v_toMonadFileMap_3046_);
v___x_3049_ = lean_apply_4(v_toBind_3044_, lean_box(0), lean_box(0), v___x_3047_, v___f_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_ex_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3051_, v_inst_3052_, v_ex_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_x_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_3055_, v_inst_3056_, v_x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_3062_, lean_object* v_inst_3063_, lean_object* v_inst_3064_, lean_object* v_____do__lift_3065_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_msg_3062_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Lean_toMessageList(v_____do__lift_3065_);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = l_Lean_throwError___redArg(v_inst_3063_, v_inst_3064_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_msg_3074_, lean_object* v_exs_3075_){
_start:
{
lean_object* v_toBind_3076_; lean_object* v___f_3077_; lean_object* v___f_3078_; size_t v_sz_3079_; size_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_toBind_3076_ = lean_ctor_get(v_inst_3072_, 1);
lean_inc(v_toBind_3076_);
lean_inc_ref_n(v_inst_3072_, 2);
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3077_, 0, v_inst_3072_);
lean_closure_set(v___f_3077_, 1, v_inst_3073_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3078_, 0, v_msg_3074_);
lean_closure_set(v___f_3078_, 1, v_inst_3072_);
lean_closure_set(v___f_3078_, 2, v_inst_3071_);
v_sz_3079_ = lean_array_size(v_exs_3075_);
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3072_, v___f_3077_, v_sz_3079_, v___x_3080_, v_exs_3075_);
v___x_3082_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v___x_3081_, v___f_3078_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_3083_, lean_object* v_00_u03b1_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_msg_3088_, lean_object* v_exs_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_3085_, v_inst_3086_, v_inst_3087_, v_msg_3088_, v_exs_3089_);
return v___x_3090_;
}
}
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3157_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3158_ = 0;
v___x_3159_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3160_ = l_Lean_registerTraceClass(v___x_3157_, v___x_3158_, v___x_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec_ref_known(v___x_3160_, 1);
v___x_3161_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3162_ = l_Lean_registerTraceClass(v___x_3161_, v___x_3158_, v___x_3159_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; 
lean_dec_ref_known(v___x_3162_, 1);
v___x_3163_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3164_ = 1;
v___x_3165_ = l_Lean_registerTraceClass(v___x_3163_, v___x_3164_, v___x_3159_);
return v___x_3165_;
}
else
{
return v___x_3162_;
}
}
else
{
return v___x_3160_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3166_;
v_res_3166_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3168_;
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
