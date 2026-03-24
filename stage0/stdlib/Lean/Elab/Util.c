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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(lean_object*, lean_object*);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
lean_object* l_EStateM_instMonadExceptOfOfBacktrackable___redArg(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_getRefPos___redArg(lean_object*, lean_object*);
lean_object* l_Lean_toMessageList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_String_toFormat(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_getBetterRef___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "macroStack"};
static const lean_object* l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(63, 33, 22, 128, 67, 155, 63, 18)}};
static const lean_object* l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "display macro expansion stack"};
static const lean_object* l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 212, 36, 208, 228, 94, 220, 119)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 94, 242, 78, 7, 86, 25, 134)}};
static const lean_object* l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "macroAttribute"};
static const lean_object* l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 124, 3, 111, 194, 84, 182, 133)}};
static const lean_object* l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute;
static const lean_string_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 391, .m_capacity = 391, .m_length = 388, .m_data = "Registers a macro expander for a given syntax node kind.\n\nA macro expander should have type `Lean.Macro` (which is `Lean.Syntax → Lean.MacroM Lean.Syntax`),\ni.e. should take syntax of the given syntax node kind as a parameter and produce different syntax\nin the same syntax category.\n\nThe `macro_rules` and `macro` commands should usually be preferred over using this attribute\ndirectly.\n"};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_liftMacroM___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_liftMacroM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_liftMacroM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 78, 200, 72, 47, 79, 142, 191)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(255, 84, 221, 213, 184, 25, 230, 28)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 230, 224, 210, 33, 91, 167, 71)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(80, 51, 41, 220, 74, 50, 181, 52)}};
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
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(151, 200, 117, 111, 119, 67, 77, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 235, 194, 189, 11, 11, 236, 225)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
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
lean_dec_ref(v___x_3_);
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
lean_object* v_imported_47_; lean_object* v_ctx_48_; lean_object* v_scopes_49_; lean_object* v_imported_50_; lean_object* v_ctx_51_; lean_object* v_scopes_52_; uint8_t v___y_54_; uint8_t v___x_56_; 
v_imported_47_ = lean_ctor_get(v_a_45_, 1);
v_ctx_48_ = lean_ctor_get(v_a_45_, 2);
v_scopes_49_ = lean_ctor_get(v_a_45_, 3);
v_imported_50_ = lean_ctor_get(v_b_46_, 1);
v_ctx_51_ = lean_ctor_get(v_b_46_, 2);
v_scopes_52_ = lean_ctor_get(v_b_46_, 3);
v___x_56_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_scopes_49_, v_scopes_52_);
if (v___x_56_ == 0)
{
v___y_54_ = v___x_56_;
goto v___jp_53_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = lean_name_eq(v_ctx_48_, v_ctx_51_);
v___y_54_ = v___x_57_;
goto v___jp_53_;
}
v___jp_53_:
{
if (v___y_54_ == 0)
{
return v___y_54_;
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
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_equalScope___boxed(lean_object* v_a_58_, lean_object* v_b_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Lean_MacroScopesView_equalScope(v_a_58_, v_b_59_);
lean_dec_ref(v_b_59_);
lean_dec_ref(v_a_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio(lean_object* v_stx_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Lean_Syntax_isNone(v_stx_71_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_75_);
v___x_77_ = ((lean_object*)(l_Lean_Elab_expandOptNamedPrio___closed__4));
lean_inc(v___x_76_);
v___x_78_ = l_Lean_Syntax_isOfKind(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec(v___x_76_);
v___x_79_ = l_Lean_Macro_throwUnsupported___redArg(v_a_73_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(3u);
v___x_81_ = l_Lean_Syntax_getArg(v___x_76_, v___x_80_);
lean_dec(v___x_76_);
v___x_82_ = l_Lean_evalPrio(v___x_81_, v_a_72_, v_a_73_);
return v___x_82_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1000u);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_a_73_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object* v_stx_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_expandOptNamedPrio(v_stx_85_, v_a_86_, v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_stx_85_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
else
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v_val_95_; uint8_t v___x_96_; 
v_val_94_ = lean_ctor_get(v_x_89_, 0);
v_val_95_ = lean_ctor_get(v_x_90_, 0);
v___x_96_ = lean_nat_dec_eq(v_val_94_, v_val_95_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_97_, v_x_98_);
lean_dec(v_x_98_);
lean_dec(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_getBetterRef___lam__0(uint8_t v___x_101_, lean_object* v___x_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_before_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_before_104_ = lean_ctor_get(v_x_103_, 0);
v___x_105_ = l_Lean_Syntax_getPos_x3f(v_before_104_, v___x_101_);
v___x_106_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v___x_105_, v___x_102_);
lean_dec(v___x_105_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
else
{
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___lam__0___boxed(lean_object* v___x_108_, lean_object* v___x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v___x_115__boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v___x_115__boxed_111_ = lean_unbox(v___x_108_);
v_res_112_ = l_Lean_Elab_getBetterRef___lam__0(v___x_115__boxed_111_, v___x_109_, v_x_110_);
lean_dec_ref(v_x_110_);
lean_dec(v___x_109_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* v_ref_114_, lean_object* v_macroStack_115_){
_start:
{
uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = 0;
v___x_117_ = l_Lean_Syntax_getPos_x3f(v_ref_114_, v___x_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(v___x_116_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Elab_getBetterRef___lam__0___boxed), 3, 2);
lean_closure_set(v___f_119_, 0, v___x_118_);
lean_closure_set(v___f_119_, 1, v___x_117_);
v___x_120_ = l_List_find_x3f___redArg(v___f_119_, v_macroStack_115_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_inc(v_ref_114_);
return v_ref_114_;
}
else
{
lean_object* v_val_121_; lean_object* v_before_122_; 
v_val_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref(v___x_120_);
v_before_122_ = lean_ctor_get(v_val_121_, 0);
lean_inc(v_before_122_);
lean_dec(v_val_121_);
return v_before_122_;
}
}
else
{
lean_dec_ref(v___x_117_);
lean_dec(v_macroStack_115_);
lean_inc(v_ref_114_);
return v_ref_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* v_ref_123_, lean_object* v_macroStack_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Elab_getBetterRef(v_ref_123_, v_macroStack_124_);
lean_dec(v_ref_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object* v_name_126_, lean_object* v_decl_127_, lean_object* v_ref_128_){
_start:
{
lean_object* v_defValue_130_; lean_object* v_descr_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_158_; 
v_defValue_130_ = lean_ctor_get(v_decl_127_, 0);
v_descr_131_ = lean_ctor_get(v_decl_127_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_decl_127_);
if (v_isSharedCheck_158_ == 0)
{
v___x_133_ = v_decl_127_;
v_isShared_134_ = v_isSharedCheck_158_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_descr_131_);
lean_inc(v_defValue_130_);
lean_dec(v_decl_127_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_158_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_alloc_ctor(1, 0, 1);
v___x_136_ = lean_unbox(v_defValue_130_);
lean_ctor_set_uint8(v___x_135_, 0, v___x_136_);
lean_inc(v_name_126_);
v___x_137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_137_, 0, v_name_126_);
lean_ctor_set(v___x_137_, 1, v_ref_128_);
lean_ctor_set(v___x_137_, 2, v___x_135_);
lean_ctor_set(v___x_137_, 3, v_descr_131_);
lean_inc(v_name_126_);
v___x_138_ = lean_register_option(v_name_126_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_148_; 
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_138_, 0);
lean_dec(v_unused_149_);
v___x_140_ = v___x_138_;
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
else
{
lean_dec(v___x_138_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_defValue_130_);
lean_ctor_set(v___x_133_, 0, v_name_126_);
v___x_143_ = v___x_133_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_name_126_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_defValue_130_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_del_object(v___x_133_);
lean_dec(v_defValue_130_);
lean_dec(v_name_126_);
v_a_150_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_138_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_138_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_159_, lean_object* v_decl_160_, lean_object* v_ref_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_159_, v_decl_160_, v_ref_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_182_ = ((lean_object*)(l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_183_ = ((lean_object*)(l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_184_ = l_Lean_Option_register___at___00Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_181_, v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_218_, lean_object* v_toApplicative_219_, lean_object* v_msgData_220_, lean_object* v_macroStack_221_, lean_object* v_____do__lift_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = l_Lean_Elab_pp_macroStack;
v___x_224_ = l_Lean_Option_get___redArg(v___x_218_, v_____do__lift_222_, v___x_223_);
v___x_225_ = lean_unbox(v___x_224_);
lean_dec(v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v_toPure_226_; lean_object* v___x_227_; 
lean_dec(v_macroStack_221_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_226_);
lean_dec_ref(v_toApplicative_219_);
v___x_227_ = lean_apply_2(v_toPure_226_, lean_box(0), v_msgData_220_);
return v___x_227_;
}
else
{
if (lean_obj_tag(v_macroStack_221_) == 0)
{
lean_object* v_toPure_228_; lean_object* v___x_229_; 
v_toPure_228_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_228_);
lean_dec_ref(v_toApplicative_219_);
v___x_229_ = lean_apply_2(v_toPure_228_, lean_box(0), v_msgData_220_);
return v___x_229_;
}
else
{
lean_object* v_head_230_; lean_object* v_after_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_248_; 
v_head_230_ = lean_ctor_get(v_macroStack_221_, 0);
lean_inc(v_head_230_);
v_after_231_ = lean_ctor_get(v_head_230_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_head_230_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_head_230_, 0);
lean_dec(v_unused_249_);
v___x_233_ = v_head_230_;
v_isShared_234_ = v_isSharedCheck_248_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_after_231_);
lean_dec(v_head_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_248_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_toPure_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___x_239_; 
v_toPure_235_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_235_);
lean_dec_ref(v_toApplicative_219_);
v___x_236_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_237_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 7);
lean_ctor_set(v___x_233_, 1, v___x_236_);
lean_ctor_set(v___x_233_, 0, v_msgData_220_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_msgData_220_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_236_);
v___x_239_ = v_reuseFailAlloc_247_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_msgData_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_240_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_MessageData_ofSyntax(v_after_231_);
v___x_243_ = l_Lean_indentD(v___x_242_);
v_msgData_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_244_, 0, v___x_241_);
lean_ctor_set(v_msgData_244_, 1, v___x_243_);
v___x_245_ = l_List_foldl___redArg(v___f_237_, v_msgData_244_, v_macroStack_221_);
v___x_246_ = lean_apply_2(v_toPure_235_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_250_, lean_object* v_toApplicative_251_, lean_object* v_msgData_252_, lean_object* v_macroStack_253_, lean_object* v_____do__lift_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_250_, v_toApplicative_251_, v_msgData_252_, v_macroStack_253_, v_____do__lift_254_);
lean_dec_ref(v_____do__lift_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_msgData_258_, lean_object* v_macroStack_259_){
_start:
{
lean_object* v___x_260_; lean_object* v_toApplicative_261_; lean_object* v_toBind_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v___x_260_ = l_Lean_KVMap_instValueBool;
v_toApplicative_261_ = lean_ctor_get(v_inst_256_, 0);
lean_inc_ref(v_toApplicative_261_);
v_toBind_262_ = lean_ctor_get(v_inst_256_, 1);
lean_inc(v_toBind_262_);
lean_dec_ref(v_inst_256_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_263_, 0, v___x_260_);
lean_closure_set(v___f_263_, 1, v_toApplicative_261_);
lean_closure_set(v___f_263_, 2, v_msgData_258_);
lean_closure_set(v___f_263_, 3, v_macroStack_259_);
v___x_264_ = lean_apply_4(v_toBind_262_, lean_box(0), lean_box(0), v_inst_257_, v___f_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_msgData_268_, lean_object* v_macroStack_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Elab_addMacroStack___redArg(v_inst_266_, v_inst_267_, v_msgData_268_, v_macroStack_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_____r_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_278_ = l_Lean_throwError___redArg(v_inst_274_, v_inst_275_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_279_, lean_object* v___f_280_, lean_object* v_toApplicative_281_, lean_object* v_____do__lift_282_){
_start:
{
uint8_t v___x_283_; 
lean_inc(v_k_279_);
v___x_283_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_282_, v_k_279_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec_ref(v_toApplicative_281_);
lean_dec(v_k_279_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_apply_1(v___f_280_, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v_toPure_286_; lean_object* v___x_287_; 
lean_dec(v___f_280_);
v_toPure_286_ = lean_ctor_get(v_toApplicative_281_, 1);
lean_inc(v_toPure_286_);
lean_dec_ref(v_toApplicative_281_);
v___x_287_ = lean_apply_2(v_toPure_286_, lean_box(0), v_k_279_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_288_, lean_object* v___f_289_, lean_object* v_toApplicative_290_, lean_object* v_toBind_291_, lean_object* v_getEnv_292_, lean_object* v_____do__lift_293_){
_start:
{
lean_object* v_k_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v_k_294_ = l_Lean_mkPrivateName(v_____do__lift_293_, v_k_288_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_295_, 0, v_k_294_);
lean_closure_set(v___f_295_, 1, v___f_289_);
lean_closure_set(v___f_295_, 2, v_toApplicative_290_);
v___x_296_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v_getEnv_292_, v___f_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_297_, lean_object* v___f_298_, lean_object* v_toApplicative_299_, lean_object* v_toBind_300_, lean_object* v_getEnv_301_, lean_object* v_____do__lift_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_297_, v___f_298_, v_toApplicative_299_, v_toBind_300_, v_getEnv_301_, v_____do__lift_302_);
lean_dec_ref(v_____do__lift_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_304_, lean_object* v_k_305_, lean_object* v_toBind_306_, lean_object* v_getEnv_307_, lean_object* v___f_308_, uint8_t v___x_309_, lean_object* v_____do__lift_310_){
_start:
{
uint8_t v_isExporting_318_; 
v_isExporting_318_ = lean_ctor_get_uint8(v_____do__lift_310_, sizeof(void*)*8);
if (v_isExporting_318_ == 0)
{
goto v___jp_314_;
}
else
{
if (v___x_309_ == 0)
{
lean_dec(v___f_308_);
lean_dec(v_getEnv_307_);
lean_dec(v_toBind_306_);
goto v___jp_311_;
}
else
{
goto v___jp_314_;
}
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v___f_304_, v___x_312_);
return v___x_313_;
}
v___jp_314_:
{
uint8_t v___x_315_; 
v___x_315_ = l_Lean_isPrivateName(v_k_305_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v___f_304_);
v___x_316_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v_getEnv_307_, v___f_308_);
return v___x_316_;
}
else
{
if (v___x_309_ == 0)
{
lean_dec(v___f_308_);
lean_dec(v_getEnv_307_);
lean_dec(v_toBind_306_);
goto v___jp_311_;
}
else
{
lean_object* v___x_317_; 
lean_dec(v___f_304_);
v___x_317_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v_getEnv_307_, v___f_308_);
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_319_, lean_object* v_k_320_, lean_object* v_toBind_321_, lean_object* v_getEnv_322_, lean_object* v___f_323_, lean_object* v___x_324_, lean_object* v_____do__lift_325_){
_start:
{
uint8_t v___x_386__boxed_326_; lean_object* v_res_327_; 
v___x_386__boxed_326_ = lean_unbox(v___x_324_);
v_res_327_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_319_, v_k_320_, v_toBind_321_, v_getEnv_322_, v___f_323_, v___x_386__boxed_326_, v_____do__lift_325_);
lean_dec_ref(v_____do__lift_325_);
lean_dec(v_k_320_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_328_, lean_object* v___f_329_, lean_object* v_toBind_330_, lean_object* v_getEnv_331_, lean_object* v___f_332_, lean_object* v_toApplicative_333_, lean_object* v_____do__lift_334_){
_start:
{
uint8_t v___x_335_; 
lean_inc(v_k_328_);
v___x_335_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_334_, v_k_328_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; 
lean_dec_ref(v_toApplicative_333_);
v___x_336_ = lean_box(v___x_335_);
lean_inc(v_getEnv_331_);
lean_inc(v_toBind_330_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_337_, 0, v___f_329_);
lean_closure_set(v___f_337_, 1, v_k_328_);
lean_closure_set(v___f_337_, 2, v_toBind_330_);
lean_closure_set(v___f_337_, 3, v_getEnv_331_);
lean_closure_set(v___f_337_, 4, v___f_332_);
lean_closure_set(v___f_337_, 5, v___x_336_);
v___x_338_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_getEnv_331_, v___f_337_);
return v___x_338_;
}
else
{
lean_object* v_toPure_339_; lean_object* v___x_340_; 
lean_dec(v___f_332_);
lean_dec(v_getEnv_331_);
lean_dec(v_toBind_330_);
lean_dec(v___f_329_);
v_toPure_339_ = lean_ctor_get(v_toApplicative_333_, 1);
lean_inc(v_toPure_339_);
lean_dec_ref(v_toApplicative_333_);
v___x_340_ = lean_apply_2(v_toPure_339_, lean_box(0), v_k_328_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_k_344_){
_start:
{
lean_object* v_toApplicative_345_; lean_object* v_toBind_346_; lean_object* v_getEnv_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_341_, 0);
lean_inc_ref(v_toApplicative_345_);
v_toBind_346_ = lean_ctor_get(v_inst_341_, 1);
lean_inc(v_toBind_346_);
v_getEnv_347_ = lean_ctor_get(v_inst_342_, 0);
lean_inc(v_getEnv_347_);
lean_dec_ref(v_inst_342_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_348_, 0, v_inst_341_);
lean_closure_set(v___f_348_, 1, v_inst_343_);
lean_inc(v_getEnv_347_);
lean_inc(v_toBind_346_);
lean_inc_ref(v_toApplicative_345_);
lean_inc_ref(v___f_348_);
lean_inc(v_k_344_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_349_, 0, v_k_344_);
lean_closure_set(v___f_349_, 1, v___f_348_);
lean_closure_set(v___f_349_, 2, v_toApplicative_345_);
lean_closure_set(v___f_349_, 3, v_toBind_346_);
lean_closure_set(v___f_349_, 4, v_getEnv_347_);
lean_inc(v_getEnv_347_);
lean_inc(v_toBind_346_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_350_, 0, v_k_344_);
lean_closure_set(v___f_350_, 1, v___f_348_);
lean_closure_set(v___f_350_, 2, v_toBind_346_);
lean_closure_set(v___f_350_, 3, v_getEnv_347_);
lean_closure_set(v___f_350_, 4, v___f_349_);
lean_closure_set(v___f_350_, 5, v_toApplicative_345_);
v___x_351_ = lean_apply_4(v_toBind_346_, lean_box(0), lean_box(0), v_getEnv_347_, v___f_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_k_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_353_, v_inst_354_, v_inst_355_, v_k_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_k_361_, lean_object* v_pre_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_358_, v_inst_359_, v_inst_360_, v_k_361_, v_pre_362_, v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_k_368_, lean_object* v_x_369_){
_start:
{
switch(lean_obj_tag(v_x_369_))
{
case 1:
{
lean_object* v_toMonadExceptOf_370_; lean_object* v_pre_371_; lean_object* v_tryCatch_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_toMonadExceptOf_370_ = lean_ctor_get(v_inst_367_, 0);
v_pre_371_ = lean_ctor_get(v_x_369_, 0);
v_tryCatch_372_ = lean_ctor_get(v_toMonadExceptOf_370_, 1);
lean_inc(v_tryCatch_372_);
lean_inc(v_pre_371_);
lean_inc(v_k_368_);
lean_inc_ref(v_inst_367_);
lean_inc_ref(v_inst_366_);
lean_inc_ref(v_inst_365_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_373_, 0, v_inst_365_);
lean_closure_set(v___f_373_, 1, v_inst_366_);
lean_closure_set(v___f_373_, 2, v_inst_367_);
lean_closure_set(v___f_373_, 3, v_k_368_);
lean_closure_set(v___f_373_, 4, v_pre_371_);
v___x_374_ = l_Lean_Name_append(v_x_369_, v_k_368_);
v___x_375_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_365_, v_inst_366_, v_inst_367_, v___x_374_);
v___x_376_ = lean_apply_3(v_tryCatch_372_, lean_box(0), v___x_375_, v___f_373_);
return v___x_376_;
}
case 0:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_365_, v_inst_366_, v_inst_367_, v_k_368_);
return v___x_377_;
}
default: 
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_x_369_);
lean_dec(v_k_368_);
lean_dec_ref(v_inst_366_);
v___x_378_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_379_ = l_Lean_throwError___redArg(v_inst_365_, v_inst_367_, v___x_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_k_383_, lean_object* v_pre_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_380_, v_inst_381_, v_inst_382_, v_k_383_, v_pre_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_k_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_388_, v_inst_389_, v_inst_390_, v_k_391_, v_x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_394_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_ctor_set(v___x_399_, 3, v___x_397_);
lean_ctor_set(v___x_399_, 4, v___x_397_);
lean_ctor_set(v___x_399_, 5, v___x_397_);
lean_ctor_set(v___x_399_, 6, v___x_397_);
lean_ctor_set(v___x_399_, 7, v___x_397_);
lean_ctor_set(v___x_399_, 8, v___x_397_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_env_418_; lean_object* v_options_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_417_ = lean_st_ref_get(v___y_415_);
v_env_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_env_418_);
lean_dec(v___x_417_);
v_options_419_ = lean_ctor_get(v___y_414_, 2);
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_419_);
v___x_422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_422_, 0, v_env_418_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_421_);
lean_ctor_set(v___x_422_, 3, v_options_419_);
v___x_423_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_msgData_413_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_ref_434_; lean_object* v___x_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_ref_434_ = lean_ctor_get(v___y_431_, 5);
v___x_435_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_430_, v___y_431_, v___y_432_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_inc(v_ref_434_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_ref_434_);
lean_ctor_set(v___x_440_, 1, v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 1);
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___x_459_; lean_object* v_env_460_; uint8_t v___x_461_; 
v___x_459_ = lean_st_ref_get(v___y_452_);
v_env_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_env_460_);
lean_dec(v___x_459_);
lean_inc(v_k_450_);
v___x_461_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_460_, v_k_450_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v_env_479_; uint8_t v_isExporting_480_; 
v___x_462_ = lean_st_ref_get(v___y_452_);
v_env_479_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_479_);
lean_dec(v___x_462_);
v_isExporting_480_ = lean_ctor_get_uint8(v_env_479_, sizeof(void*)*8);
lean_dec_ref(v_env_479_);
if (v_isExporting_480_ == 0)
{
goto v___jp_463_;
}
else
{
if (v___x_461_ == 0)
{
lean_dec(v_k_450_);
v___y_455_ = v___y_451_;
v___y_456_ = v___y_452_;
goto v___jp_454_;
}
else
{
goto v___jp_463_;
}
}
v___jp_463_:
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_isPrivateName(v_k_450_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_env_466_; lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v_k_469_; uint8_t v___x_470_; 
v___x_465_ = lean_st_ref_get(v___y_452_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_env_466_);
lean_dec(v___x_465_);
v___x_467_ = lean_st_ref_get(v___y_452_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v_k_469_ = l_Lean_mkPrivateName(v_env_466_, v_k_450_);
lean_dec_ref(v_env_466_);
lean_inc(v_k_469_);
v___x_470_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_468_, v_k_469_);
if (v___x_470_ == 0)
{
lean_dec(v_k_469_);
v___y_455_ = v___y_451_;
v___y_456_ = v___y_452_;
goto v___jp_454_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_k_469_);
return v___x_471_;
}
}
else
{
if (v___x_461_ == 0)
{
lean_dec(v_k_450_);
v___y_455_ = v___y_451_;
v___y_456_ = v___y_452_;
goto v___jp_454_;
}
else
{
lean_object* v___x_472_; lean_object* v_env_473_; lean_object* v___x_474_; lean_object* v_env_475_; lean_object* v_k_476_; uint8_t v___x_477_; 
v___x_472_ = lean_st_ref_get(v___y_452_);
v_env_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_ref(v_env_473_);
lean_dec(v___x_472_);
v___x_474_ = lean_st_ref_get(v___y_452_);
v_env_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_env_475_);
lean_dec(v___x_474_);
v_k_476_ = l_Lean_mkPrivateName(v_env_473_, v_k_450_);
lean_dec_ref(v_env_473_);
lean_inc(v_k_476_);
v___x_477_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_475_, v_k_476_);
if (v___x_477_ == 0)
{
lean_dec(v_k_476_);
v___y_455_ = v___y_451_;
v___y_456_ = v___y_452_;
goto v___jp_454_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_k_476_);
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_k_450_);
return v___x_481_;
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_458_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_457_, v___y_455_, v___y_456_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
switch(lean_obj_tag(v_x_488_))
{
case 1:
{
lean_object* v_pre_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_pre_492_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_pre_492_);
lean_inc(v_k_487_);
v___x_493_ = l_Lean_Name_append(v_x_488_, v_k_487_);
v___x_494_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_493_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_dec(v_pre_492_);
lean_dec(v_k_487_);
return v___x_494_;
}
else
{
lean_object* v_a_495_; uint8_t v___y_497_; uint8_t v___x_499_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
v___x_499_ = l_Lean_Exception_isInterrupt(v_a_495_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_Exception_isRuntime(v_a_495_);
v___y_497_ = v___x_500_;
goto v___jp_496_;
}
else
{
lean_dec(v_a_495_);
v___y_497_ = v___x_499_;
goto v___jp_496_;
}
v___jp_496_:
{
if (v___y_497_ == 0)
{
lean_dec_ref(v___x_494_);
v_x_488_ = v_pre_492_;
goto _start;
}
else
{
lean_dec(v_pre_492_);
lean_dec(v_k_487_);
return v___x_494_;
}
}
}
}
case 0:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_487_, v___y_489_, v___y_490_);
return v___x_501_;
}
default: 
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_x_488_);
lean_dec(v_k_487_);
v___x_502_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_503_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_502_, v___y_489_, v___y_490_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_504_, v_x_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_currNamespace_514_; lean_object* v___x_515_; 
v_currNamespace_514_ = lean_ctor_get(v_a_511_, 6);
lean_inc(v_currNamespace_514_);
v___x_515_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_510_, v_currNamespace_514_, v_a_511_, v_a_512_);
lean_dec_ref(v_a_511_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_521_, lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_522_, v___y_523_, v___y_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_527_, lean_object* v_msg_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_527_, v_msg_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_532_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_539_, lean_object* v_stx_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Attribute_Builtin_getId(v_stx_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v___x_555_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v___x_544_);
lean_inc_ref(v_a_541_);
lean_inc(v_a_545_);
v___x_555_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_545_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec(v_a_545_);
lean_dec(v_defaultParserNamespace_539_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; uint8_t v___y_558_; uint8_t v___x_564_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v___x_564_ = l_Lean_Exception_isInterrupt(v_a_556_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; 
v___x_565_ = l_Lean_Exception_isRuntime(v_a_556_);
v___y_558_ = v___x_565_;
goto v___jp_557_;
}
else
{
lean_dec(v_a_556_);
v___y_558_ = v___x_564_;
goto v___jp_557_;
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v___x_555_);
lean_inc(v_a_545_);
v___x_559_ = l_Lean_Name_append(v_defaultParserNamespace_539_, v_a_545_);
v___x_560_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_559_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec(v_a_545_);
return v___x_560_;
}
else
{
lean_object* v_a_561_; uint8_t v___x_562_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
v___x_562_ = l_Lean_Exception_isInterrupt(v_a_561_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
v___x_563_ = l_Lean_Exception_isRuntime(v_a_561_);
v___y_547_ = v___x_560_;
v___y_548_ = v___x_563_;
goto v___jp_546_;
}
else
{
lean_dec(v_a_561_);
v___y_547_ = v___x_560_;
v___y_548_ = v___x_562_;
goto v___jp_546_;
}
}
}
else
{
lean_dec(v_a_545_);
lean_dec(v_defaultParserNamespace_539_);
return v___x_555_;
}
}
}
v___jp_546_:
{
if (v___y_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v___y_547_);
v___x_549_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_550_ = l_Lean_MessageData_ofName(v_a_545_);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_553_, v_a_541_, v_a_542_);
return v___x_554_;
}
else
{
lean_dec(v_a_545_);
return v___y_547_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_539_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_566_, lean_object* v_stx_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_566_, v_stx_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_576_, lean_object* v_opts_577_, lean_object* v_constName_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_580_ = l_Lean_Environment_evalConstCheck___redArg(v_env_576_, v_opts_577_, v___x_579_, v_constName_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_581_, lean_object* v_opts_582_, lean_object* v_constName_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_581_, v_opts_582_, v_constName_583_);
lean_dec_ref(v_opts_582_);
return v_res_584_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_610_ = l_Lean_mkAtom(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_612_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_613_ = lean_array_push(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_623_ = l_Lean_mkAtom(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_625_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_626_ = lean_array_push(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_628_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_629_ = lean_box(2);
v___x_630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_627_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_632_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_633_ = lean_array_push(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_635_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_636_ = lean_box(2);
v___x_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_634_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_639_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_640_ = lean_array_push(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_642_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_643_ = lean_box(2);
v___x_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_641_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_646_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_647_ = lean_array_push(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_649_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_650_ = lean_box(2);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_653_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_654_ = lean_array_push(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_655_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_656_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_657_ = lean_box(2);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_655_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_660_, lean_object* v_declName_661_, lean_object* v_kind_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
if (v_builtin_660_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v_declName_661_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_661_, v___y_663_, v___y_664_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_669_, lean_object* v_declName_670_, lean_object* v_kind_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_builtin_boxed_675_; lean_object* v_res_676_; 
v_builtin_boxed_675_ = lean_unbox(v_builtin_669_);
v_res_676_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_675_, v_declName_670_, v_kind_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v_kind_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(lean_object* v_t_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v_infoState_681_; uint8_t v_enabled_682_; 
v___x_680_ = lean_st_ref_get(v___y_678_);
v_infoState_681_ = lean_ctor_get(v___x_680_, 7);
lean_inc_ref(v_infoState_681_);
lean_dec(v___x_680_);
v_enabled_682_ = lean_ctor_get_uint8(v_infoState_681_, sizeof(void*)*3);
lean_dec_ref(v_infoState_681_);
if (v_enabled_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref(v_t_677_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v_infoState_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_cache_692_; lean_object* v_messages_693_; lean_object* v_snapshotTasks_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_716_; 
v___x_685_ = lean_st_ref_take(v___y_678_);
v_infoState_686_ = lean_ctor_get(v___x_685_, 7);
v_env_687_ = lean_ctor_get(v___x_685_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_685_, 1);
v_ngen_689_ = lean_ctor_get(v___x_685_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_685_, 3);
v_traceState_691_ = lean_ctor_get(v___x_685_, 4);
v_cache_692_ = lean_ctor_get(v___x_685_, 5);
v_messages_693_ = lean_ctor_get(v___x_685_, 6);
v_snapshotTasks_694_ = lean_ctor_get(v___x_685_, 8);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_716_ == 0)
{
v___x_696_ = v___x_685_;
v_isShared_697_ = v_isSharedCheck_716_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snapshotTasks_694_);
lean_inc(v_infoState_686_);
lean_inc(v_messages_693_);
lean_inc(v_cache_692_);
lean_inc(v_traceState_691_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_685_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_716_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v_enabled_698_; lean_object* v_assignment_699_; lean_object* v_lazyAssignment_700_; lean_object* v_trees_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_715_; 
v_enabled_698_ = lean_ctor_get_uint8(v_infoState_686_, sizeof(void*)*3);
v_assignment_699_ = lean_ctor_get(v_infoState_686_, 0);
v_lazyAssignment_700_ = lean_ctor_get(v_infoState_686_, 1);
v_trees_701_ = lean_ctor_get(v_infoState_686_, 2);
v_isSharedCheck_715_ = !lean_is_exclusive(v_infoState_686_);
if (v_isSharedCheck_715_ == 0)
{
v___x_703_ = v_infoState_686_;
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_trees_701_);
lean_inc(v_lazyAssignment_700_);
lean_inc(v_assignment_699_);
lean_dec(v_infoState_686_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_PersistentArray_push___redArg(v_trees_701_, v_t_677_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 2, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_assignment_699_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_lazyAssignment_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v___x_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*3, v_enabled_698_);
v___x_707_ = v_reuseFailAlloc_714_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 7, v___x_707_);
v___x_709_ = v___x_696_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_env_687_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_traceState_691_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v_cache_692_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_messages_693_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_713_, 8, v_snapshotTasks_694_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_st_ref_set(v___y_678_, v___x_709_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_t_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(v_t_717_, v___y_718_);
lean_dec(v___y_718_);
return v_res_720_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(32u);
v___x_722_ = lean_mk_empty_array_with_capacity(v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_724_ = ((size_t)5ULL);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_unsigned_to_nat(32u);
v___x_727_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_728_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_729_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_725_);
lean_ctor_set(v___x_729_, 3, v___x_725_);
lean_ctor_set_usize(v___x_729_, 4, v___x_724_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v_infoState_735_; uint8_t v_enabled_736_; 
v___x_734_ = lean_st_ref_get(v___y_732_);
v_infoState_735_ = lean_ctor_get(v___x_734_, 7);
lean_inc_ref(v_infoState_735_);
lean_dec(v___x_734_);
v_enabled_736_ = lean_ctor_get_uint8(v_infoState_735_, sizeof(void*)*3);
lean_dec_ref(v_infoState_735_);
if (v_enabled_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec_ref(v_t_730_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_t_730_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(v___x_740_, v___y_732_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_746_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_768_, lean_object* v_declHint_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_env_773_; uint8_t v___x_774_; 
v___x_772_ = lean_st_ref_get(v___y_770_);
v_env_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_env_773_);
lean_dec(v___x_772_);
v___x_774_ = l_Lean_Name_isAnonymous(v_declHint_769_);
if (v___x_774_ == 0)
{
uint8_t v_isExporting_775_; 
v_isExporting_775_ = lean_ctor_get_uint8(v_env_773_, sizeof(void*)*8);
if (v_isExporting_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v_env_773_);
lean_dec(v_declHint_769_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_msg_768_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; 
lean_inc_ref(v_env_773_);
v___x_777_ = l_Lean_Environment_setExporting(v_env_773_, v___x_774_);
lean_inc(v_declHint_769_);
lean_inc_ref(v___x_777_);
v___x_778_ = l_Lean_Environment_contains(v___x_777_, v_declHint_769_, v_isExporting_775_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v___x_777_);
lean_dec_ref(v_env_773_);
lean_dec(v_declHint_769_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_msg_768_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_c_785_; lean_object* v___x_786_; 
v___x_780_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_781_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_782_ = l_Lean_Options_empty;
v___x_783_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_783_, 0, v___x_777_);
lean_ctor_set(v___x_783_, 1, v___x_780_);
lean_ctor_set(v___x_783_, 2, v___x_781_);
lean_ctor_set(v___x_783_, 3, v___x_782_);
lean_inc(v_declHint_769_);
v___x_784_ = l_Lean_MessageData_ofConstName(v_declHint_769_, v___x_774_);
v_c_785_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_785_, 0, v___x_783_);
lean_ctor_set(v_c_785_, 1, v___x_784_);
v___x_786_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_773_, v_declHint_769_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_env_773_);
lean_dec(v_declHint_769_);
v___x_787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_c_785_);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = l_Lean_MessageData_note(v___x_790_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v_msg_768_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_829_; 
v_val_794_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_829_ == 0)
{
v___x_796_ = v___x_786_;
v_isShared_797_ = v_isSharedCheck_829_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v___x_786_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_829_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_mod_801_; uint8_t v___x_802_; 
v___x_798_ = lean_box(0);
v___x_799_ = l_Lean_Environment_header(v_env_773_);
lean_dec_ref(v_env_773_);
v___x_800_ = l_Lean_EnvironmentHeader_moduleNames(v___x_799_);
v_mod_801_ = lean_array_get(v___x_798_, v___x_800_, v_val_794_);
lean_dec(v_val_794_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_isPrivateName(v_declHint_769_);
lean_dec(v_declHint_769_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_c_785_);
v___x_805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_MessageData_ofName(v_mod_801_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_MessageData_note(v___x_810_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v_msg_768_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
lean_ctor_set(v___x_796_, 0, v___x_812_);
v___x_814_ = v___x_796_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_c_785_);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_MessageData_ofName(v_mod_801_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_MessageData_note(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v_msg_768_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
lean_ctor_set(v___x_796_, 0, v___x_825_);
v___x_827_ = v___x_796_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_830_; 
lean_dec_ref(v_env_773_);
lean_dec(v_declHint_769_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_msg_768_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_831_, lean_object* v_declHint_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_831_, v_declHint_832_, v___y_833_);
lean_dec(v___y_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18(lean_object* v_msg_836_, lean_object* v_declHint_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v___x_841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_836_, v_declHint_837_, v___y_839_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_851_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = l_Lean_unknownIdentifierMessageTag;
v___x_847_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_a_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_852_, lean_object* v_declHint_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18(v_msg_852_, v_declHint_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_858_, lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_fileName_863_; lean_object* v_fileMap_864_; lean_object* v_options_865_; lean_object* v_currRecDepth_866_; lean_object* v_maxRecDepth_867_; lean_object* v_ref_868_; lean_object* v_currNamespace_869_; lean_object* v_openDecls_870_; lean_object* v_initHeartbeats_871_; lean_object* v_maxHeartbeats_872_; lean_object* v_quotContext_873_; lean_object* v_currMacroScope_874_; uint8_t v_diag_875_; lean_object* v_cancelTk_x3f_876_; uint8_t v_suppressElabErrors_877_; lean_object* v_inheritedTraceOptions_878_; lean_object* v_ref_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_fileName_863_ = lean_ctor_get(v___y_860_, 0);
v_fileMap_864_ = lean_ctor_get(v___y_860_, 1);
v_options_865_ = lean_ctor_get(v___y_860_, 2);
v_currRecDepth_866_ = lean_ctor_get(v___y_860_, 3);
v_maxRecDepth_867_ = lean_ctor_get(v___y_860_, 4);
v_ref_868_ = lean_ctor_get(v___y_860_, 5);
v_currNamespace_869_ = lean_ctor_get(v___y_860_, 6);
v_openDecls_870_ = lean_ctor_get(v___y_860_, 7);
v_initHeartbeats_871_ = lean_ctor_get(v___y_860_, 8);
v_maxHeartbeats_872_ = lean_ctor_get(v___y_860_, 9);
v_quotContext_873_ = lean_ctor_get(v___y_860_, 10);
v_currMacroScope_874_ = lean_ctor_get(v___y_860_, 11);
v_diag_875_ = lean_ctor_get_uint8(v___y_860_, sizeof(void*)*14);
v_cancelTk_x3f_876_ = lean_ctor_get(v___y_860_, 12);
v_suppressElabErrors_877_ = lean_ctor_get_uint8(v___y_860_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_878_ = lean_ctor_get(v___y_860_, 13);
v_ref_879_ = l_Lean_replaceRef(v_ref_858_, v_ref_868_);
lean_inc_ref(v_inheritedTraceOptions_878_);
lean_inc(v_cancelTk_x3f_876_);
lean_inc(v_currMacroScope_874_);
lean_inc(v_quotContext_873_);
lean_inc(v_maxHeartbeats_872_);
lean_inc(v_initHeartbeats_871_);
lean_inc(v_openDecls_870_);
lean_inc(v_currNamespace_869_);
lean_inc(v_maxRecDepth_867_);
lean_inc(v_currRecDepth_866_);
lean_inc_ref(v_options_865_);
lean_inc_ref(v_fileMap_864_);
lean_inc_ref(v_fileName_863_);
v___x_880_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_880_, 0, v_fileName_863_);
lean_ctor_set(v___x_880_, 1, v_fileMap_864_);
lean_ctor_set(v___x_880_, 2, v_options_865_);
lean_ctor_set(v___x_880_, 3, v_currRecDepth_866_);
lean_ctor_set(v___x_880_, 4, v_maxRecDepth_867_);
lean_ctor_set(v___x_880_, 5, v_ref_879_);
lean_ctor_set(v___x_880_, 6, v_currNamespace_869_);
lean_ctor_set(v___x_880_, 7, v_openDecls_870_);
lean_ctor_set(v___x_880_, 8, v_initHeartbeats_871_);
lean_ctor_set(v___x_880_, 9, v_maxHeartbeats_872_);
lean_ctor_set(v___x_880_, 10, v_quotContext_873_);
lean_ctor_set(v___x_880_, 11, v_currMacroScope_874_);
lean_ctor_set(v___x_880_, 12, v_cancelTk_x3f_876_);
lean_ctor_set(v___x_880_, 13, v_inheritedTraceOptions_878_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*14, v_diag_875_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*14 + 1, v_suppressElabErrors_877_);
v___x_881_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_859_, v___x_880_, v___y_861_);
lean_dec_ref(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_882_, lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_882_, v_msg_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v_ref_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(lean_object* v_ref_888_, lean_object* v_msg_889_, lean_object* v_declHint_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_a_895_; lean_object* v___x_896_; 
v___x_894_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18(v_msg_889_, v_declHint_890_, v___y_891_, v___y_892_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_888_, v_a_895_, v___y_891_, v___y_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_ref_897_, lean_object* v_msg_898_, lean_object* v_declHint_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_897_, v_msg_898_, v_declHint_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v_ref_897_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__0));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(lean_object* v_ref_907_, lean_object* v_constName_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_912_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1);
v___x_913_ = 0;
lean_inc(v_constName_908_);
v___x_914_ = l_Lean_MessageData_ofConstName(v_constName_908_, v___x_913_);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_912_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_907_, v___x_917_, v_constName_908_, v___y_909_, v___y_910_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_ref_919_, lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_919_, v_constName_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v_ref_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_ref_929_; lean_object* v___x_930_; 
v_ref_929_ = lean_ctor_get(v___y_926_, 5);
v___x_930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_929_, v_constName_925_, v___y_926_, v___y_927_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v_env_941_; uint8_t v___x_942_; lean_object* v___x_943_; 
v___x_940_ = lean_st_ref_get(v___y_938_);
v_env_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_ref(v_env_941_);
lean_dec(v___x_940_);
v___x_942_ = 0;
lean_inc(v_constName_936_);
v___x_943_ = l_Lean_Environment_findConstVal_x3f(v_env_941_, v_constName_936_, v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_936_, v___y_937_, v___y_938_);
return v___x_944_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_constName_936_);
v_val_945_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9___boxed(lean_object* v_constName_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_constName_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__10(lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
if (lean_obj_tag(v_a_958_) == 0)
{
lean_object* v___x_960_; 
v___x_960_ = l_List_reverse___redArg(v_a_959_);
return v___x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_head_961_ = lean_ctor_get(v_a_958_, 0);
v_tail_962_ = lean_ctor_get(v_a_958_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v_a_958_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_head_961_);
lean_dec(v_a_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_mkLevelParam(v_head_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_a_959_);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_959_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_a_958_ = v_tail_962_;
v_a_959_ = v___x_968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
lean_inc(v_constName_972_);
v___x_976_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_constName_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_988_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_988_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_levelParams_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v_levelParams_981_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_levelParams_981_);
lean_dec(v_a_977_);
v___x_982_ = lean_box(0);
v___x_983_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__10(v_levelParams_981_, v___x_982_);
v___x_984_ = l_Lean_mkConst(v_constName_972_, v___x_983_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_984_);
v___x_986_ = v___x_979_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_constName_972_);
v_a_989_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_976_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_976_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_1002_, lean_object* v_n_1003_, lean_object* v_expectedType_x3f_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_1003_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_stx_1002_);
v___x_1012_ = l_Lean_LocalContext_empty;
v___x_1013_ = 0;
v___x_1014_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
lean_ctor_set(v___x_1014_, 2, v_expectedType_x3f_1004_);
lean_ctor_set(v___x_1014_, 3, v_a_1009_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*4, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*4 + 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1015_, v___y_1005_, v___y_1006_);
return v___x_1016_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_expectedType_x3f_1004_);
lean_dec(v_stx_1002_);
v_a_1017_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1008_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1008_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1025_, lean_object* v_n_1026_, lean_object* v_expectedType_x3f_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1025_, v_n_1026_, v_expectedType_x3f_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_keys_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_keys_1032_);
v___x_1036_ = lean_nat_dec_lt(v_i_1033_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec(v_i_1033_);
return v___x_1036_;
}
else
{
lean_object* v_k_x27_1037_; uint8_t v___x_1038_; 
v_k_x27_1037_ = lean_array_fget_borrowed(v_keys_1032_, v_i_1033_);
v___x_1038_ = l_Lean_instBEqExtraModUse_beq(v_k_1034_, v_k_x27_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_i_1033_, v___x_1039_);
lean_dec(v_i_1033_);
v_i_1033_ = v___x_1040_;
goto _start;
}
else
{
lean_dec(v_i_1033_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_keys_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_res_1045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_1042_, v_i_1043_, v_k_1044_);
lean_dec_ref(v_k_1044_);
lean_dec_ref(v_keys_1042_);
v_r_1046_ = lean_box(v_res_1045_);
return v_r_1046_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; 
v___x_1047_ = ((size_t)5ULL);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_shift_left(v___x_1048_, v___x_1047_);
return v___x_1049_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; 
v___x_1050_ = ((size_t)1ULL);
v___x_1051_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1052_ = lean_usize_sub(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1053_, size_t v_x_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v_es_1056_; lean_object* v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; lean_object* v_j_1061_; lean_object* v___x_1062_; 
v_es_1056_ = lean_ctor_get(v_x_1053_, 0);
lean_inc_ref(v_es_1056_);
lean_dec_ref(v_x_1053_);
v___x_1057_ = lean_box(2);
v___x_1058_ = ((size_t)5ULL);
v___x_1059_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1060_ = lean_usize_land(v_x_1054_, v___x_1059_);
v_j_1061_ = lean_usize_to_nat(v___x_1060_);
v___x_1062_ = lean_array_get(v___x_1057_, v_es_1056_, v_j_1061_);
lean_dec(v_j_1061_);
lean_dec_ref(v_es_1056_);
switch(lean_obj_tag(v___x_1062_))
{
case 0:
{
lean_object* v_key_1063_; uint8_t v___x_1064_; 
v_key_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_key_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = l_Lean_instBEqExtraModUse_beq(v_x_1055_, v_key_1063_);
lean_dec(v_key_1063_);
return v___x_1064_;
}
case 1:
{
lean_object* v_node_1065_; size_t v___x_1066_; 
v_node_1065_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_node_1065_);
lean_dec_ref(v___x_1062_);
v___x_1066_ = lean_usize_shift_right(v_x_1054_, v___x_1058_);
v_x_1053_ = v_node_1065_;
v_x_1054_ = v___x_1066_;
goto _start;
}
default: 
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
return v___x_1068_;
}
}
}
else
{
lean_object* v_ks_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_ks_1069_ = lean_ctor_get(v_x_1053_, 0);
lean_inc_ref(v_ks_1069_);
lean_dec_ref(v_x_1053_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_ks_1069_, v___x_1070_, v_x_1055_);
lean_dec_ref(v_ks_1069_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
size_t v_x_6676__boxed_1075_; uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_x_6676__boxed_1075_ = lean_unbox_usize(v_x_1073_);
lean_dec(v_x_1073_);
v_res_1076_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1072_, v_x_6676__boxed_1075_, v_x_1074_);
lean_dec_ref(v_x_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
uint64_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = l_Lean_instHashableExtraModUse_hash(v_x_1079_);
v___x_1081_ = lean_uint64_to_usize(v___x_1080_);
v___x_1082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1078_, v___x_1081_, v_x_1079_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1083_, v_x_1084_);
lean_dec_ref(v_x_1084_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_options_1093_; uint8_t v_hasTrace_1094_; 
v_options_1093_ = lean_ctor_get(v___y_1091_, 2);
v_hasTrace_1094_ = lean_ctor_get_uint8(v_options_1093_, sizeof(void*)*1);
if (v_hasTrace_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_cls_1090_);
v___x_1095_ = lean_box(v_hasTrace_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
else
{
lean_object* v_inheritedTraceOptions_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_inheritedTraceOptions_1097_ = lean_ctor_get(v___y_1091_, 13);
v___x_1098_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1099_ = l_Lean_Name_append(v___x_1098_, v_cls_1090_);
v___x_1100_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1097_, v_options_1093_, v___x_1099_);
lean_dec(v___x_1099_);
v___x_1101_ = lean_box(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1103_, v___y_1104_);
lean_dec_ref(v___y_1104_);
return v_res_1106_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1107_; double v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_float_of_nat(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(lean_object* v_cls_1112_, lean_object* v_msg_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1163_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 5);
v___x_1118_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1113_, v___y_1114_, v___y_1115_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1163_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1163_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v_traceState_1124_; lean_object* v_env_1125_; lean_object* v_nextMacroScope_1126_; lean_object* v_ngen_1127_; lean_object* v_auxDeclNGen_1128_; lean_object* v_cache_1129_; lean_object* v_messages_1130_; lean_object* v_infoState_1131_; lean_object* v_snapshotTasks_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1162_; 
v___x_1123_ = lean_st_ref_take(v___y_1115_);
v_traceState_1124_ = lean_ctor_get(v___x_1123_, 4);
v_env_1125_ = lean_ctor_get(v___x_1123_, 0);
v_nextMacroScope_1126_ = lean_ctor_get(v___x_1123_, 1);
v_ngen_1127_ = lean_ctor_get(v___x_1123_, 2);
v_auxDeclNGen_1128_ = lean_ctor_get(v___x_1123_, 3);
v_cache_1129_ = lean_ctor_get(v___x_1123_, 5);
v_messages_1130_ = lean_ctor_get(v___x_1123_, 6);
v_infoState_1131_ = lean_ctor_get(v___x_1123_, 7);
v_snapshotTasks_1132_ = lean_ctor_get(v___x_1123_, 8);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1134_ = v___x_1123_;
v_isShared_1135_ = v_isSharedCheck_1162_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snapshotTasks_1132_);
lean_inc(v_infoState_1131_);
lean_inc(v_messages_1130_);
lean_inc(v_cache_1129_);
lean_inc(v_traceState_1124_);
lean_inc(v_auxDeclNGen_1128_);
lean_inc(v_ngen_1127_);
lean_inc(v_nextMacroScope_1126_);
lean_inc(v_env_1125_);
lean_dec(v___x_1123_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1162_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint64_t v_tid_1136_; lean_object* v_traces_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_tid_1136_ = lean_ctor_get_uint64(v_traceState_1124_, sizeof(void*)*1);
v_traces_1137_ = lean_ctor_get(v_traceState_1124_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_traceState_1124_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v_traceState_1124_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_traces_1137_);
lean_dec(v_traceState_1124_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; double v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0);
v___x_1143_ = 0;
v___x_1144_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1));
v___x_1145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1145_, 0, v_cls_1112_);
lean_ctor_set(v___x_1145_, 1, v___x_1141_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3, v___x_1142_);
lean_ctor_set_float(v___x_1145_, sizeof(void*)*3 + 8, v___x_1142_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 16, v___x_1143_);
v___x_1146_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__2));
v___x_1147_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v_a_1119_);
lean_ctor_set(v___x_1147_, 2, v___x_1146_);
lean_inc(v_ref_1117_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_ref_1117_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_PersistentArray_push___redArg(v_traces_1137_, v___x_1148_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1149_);
v___x_1151_ = v___x_1139_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1149_);
lean_ctor_set_uint64(v_reuseFailAlloc_1160_, sizeof(void*)*1, v_tid_1136_);
v___x_1151_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v___x_1151_);
v___x_1153_ = v___x_1134_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_env_1125_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_nextMacroScope_1126_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_ngen_1127_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_auxDeclNGen_1128_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_cache_1129_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_messages_1130_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_infoState_1131_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_snapshotTasks_1132_);
v___x_1153_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_st_ref_set(v___y_1115_, v___x_1153_);
v___x_1155_ = lean_box(0);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1155_);
v___x_1157_ = v___x_1121_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_1164_, lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(v_cls_1164_, v_msg_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1169_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1174_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1));
v___x_1190_ = l_Lean_stringToMessageData(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1201_, uint8_t v_isMeta_1202_, lean_object* v_hint_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_env_1208_; uint8_t v_isExporting_1209_; lean_object* v___x_1210_; lean_object* v_env_1211_; lean_object* v___x_1212_; lean_object* v_entry_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___y_1218_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
v_isExporting_1209_ = lean_ctor_get_uint8(v_env_1208_, sizeof(void*)*8);
lean_dec_ref(v_env_1208_);
v___x_1210_ = lean_st_ref_get(v___y_1205_);
v_env_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_ref(v_env_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1201_);
v_entry_1213_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1213_, 0, v_mod_1201_);
lean_ctor_set_uint8(v_entry_1213_, sizeof(void*)*1, v_isExporting_1209_);
lean_ctor_set_uint8(v_entry_1213_, sizeof(void*)*1 + 1, v_isMeta_1202_);
v___x_1214_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1215_ = lean_box(1);
v___x_1216_ = lean_box(0);
v___x_1243_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1212_, v___x_1214_, v_env_1211_, v___x_1215_, v___x_1216_);
v___x_1244_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1243_, v_entry_1213_);
if (v___x_1244_ == 0)
{
lean_object* v_cls_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1254_; lean_object* v___y_1255_; uint8_t v___x_1267_; 
v_cls_1245_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1246_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1245_, v___y_1204_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1267_ = lean_unbox(v_a_1247_);
lean_dec(v_a_1247_);
if (v___x_1267_ == 0)
{
lean_dec(v_hint_1203_);
lean_dec(v_mod_1201_);
v___y_1218_ = v___y_1205_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1268_; lean_object* v___y_1270_; 
v___x_1268_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1209_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1270_ = v___x_1277_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1270_ = v___x_1278_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = l_Lean_stringToMessageData(v___y_1270_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1268_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
if (v_isMeta_1202_ == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1254_ = v___x_1274_;
v___y_1255_ = v___x_1275_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1254_ = v___x_1274_;
v___y_1255_ = v___x_1276_;
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
v___x_1252_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(v_cls_1245_, v___x_1251_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref(v___x_1252_);
v___y_1218_ = v___y_1205_;
goto v___jp_1217_;
}
else
{
lean_dec_ref(v_entry_1213_);
return v___x_1252_;
}
}
v___jp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1256_ = l_Lean_stringToMessageData(v___y_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_MessageData_ofName(v_mod_1201_);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_Name_isAnonymous(v_hint_1203_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1264_ = l_Lean_MessageData_ofName(v_hint_1203_);
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
lean_dec(v_hint_1203_);
v___x_1266_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1249_ = v___x_1261_;
v___y_1250_ = v___x_1266_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v_entry_1213_);
lean_dec(v_hint_1203_);
lean_dec(v_mod_1201_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
v___jp_1217_:
{
lean_object* v___x_1219_; lean_object* v_toEnvExtension_1220_; lean_object* v_env_1221_; lean_object* v_nextMacroScope_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_messages_1226_; lean_object* v_infoState_1227_; lean_object* v_snapshotTasks_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1241_; 
v___x_1219_ = lean_st_ref_take(v___y_1218_);
v_toEnvExtension_1220_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_toEnvExtension_1220_);
v_env_1221_ = lean_ctor_get(v___x_1219_, 0);
v_nextMacroScope_1222_ = lean_ctor_get(v___x_1219_, 1);
v_ngen_1223_ = lean_ctor_get(v___x_1219_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1219_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1219_, 4);
v_messages_1226_ = lean_ctor_get(v___x_1219_, 6);
v_infoState_1227_ = lean_ctor_get(v___x_1219_, 7);
v_snapshotTasks_1228_ = lean_ctor_get(v___x_1219_, 8);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1219_, 5);
lean_dec(v_unused_1242_);
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1241_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snapshotTasks_1228_);
lean_inc(v_infoState_1227_);
lean_inc(v_messages_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_nextMacroScope_1222_);
lean_inc(v_env_1221_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1241_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_asyncMode_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v_asyncMode_1232_ = lean_ctor_get(v_toEnvExtension_1220_, 2);
lean_inc(v_asyncMode_1232_);
lean_dec_ref(v_toEnvExtension_1220_);
v___x_1233_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1214_, v_env_1221_, v_entry_1213_, v_asyncMode_1232_, v___x_1216_);
lean_dec(v_asyncMode_1232_);
v___x_1234_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 5, v___x_1234_);
lean_ctor_set(v___x_1230_, 0, v___x_1233_);
v___x_1236_ = v___x_1230_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_nextMacroScope_1222_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1240_, 6, v_messages_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 7, v_infoState_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 8, v_snapshotTasks_1228_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_st_ref_set(v___y_1218_, v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1281_, lean_object* v_isMeta_1282_, lean_object* v_hint_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v_isMeta_boxed_1287_; lean_object* v_res_1288_; 
v_isMeta_boxed_1287_ = lean_unbox(v_isMeta_1282_);
v_res_1288_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1281_, v_isMeta_boxed_1287_, v_hint_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1289_, lean_object* v_declName_1290_, lean_object* v_as_1291_, size_t v_sz_1292_, size_t v_i_1293_, lean_object* v_b_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_lt(v_i_1293_, v_sz_1292_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v_declName_1290_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_b_1294_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v_modules_1301_; lean_object* v___x_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v_toImport_1305_; lean_object* v_module_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1300_ = l_Lean_Environment_header(v___x_1289_);
v_modules_1301_ = lean_ctor_get(v___x_1300_, 3);
lean_inc_ref(v_modules_1301_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1303_ = lean_array_uget_borrowed(v_as_1291_, v_i_1293_);
v___x_1304_ = lean_array_get(v___x_1302_, v_modules_1301_, v_a_1303_);
lean_dec_ref(v_modules_1301_);
v_toImport_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_ref(v_toImport_1305_);
lean_dec(v___x_1304_);
v_module_1306_ = lean_ctor_get(v_toImport_1305_, 0);
lean_inc(v_module_1306_);
lean_dec_ref(v_toImport_1305_);
v___x_1307_ = 0;
lean_inc(v_declName_1290_);
v___x_1308_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1306_, v___x_1307_, v_declName_1290_, v___y_1295_, v___y_1296_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; 
lean_dec_ref(v___x_1308_);
v___x_1309_ = lean_box(0);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_add(v_i_1293_, v___x_1310_);
v_i_1293_ = v___x_1311_;
v_b_1294_ = v___x_1309_;
goto _start;
}
else
{
lean_dec(v_declName_1290_);
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1313_, lean_object* v_declName_1314_, lean_object* v_as_1315_, lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
size_t v_sz_boxed_1322_; size_t v_i_boxed_1323_; lean_object* v_res_1324_; 
v_sz_boxed_1322_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1323_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1313_, v_declName_1314_, v_as_1315_, v_sz_boxed_1322_, v_i_boxed_1323_, v_b_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_as_1315_);
lean_dec_ref(v___x_1313_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(lean_object* v_a_1325_, lean_object* v_x_1326_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
else
{
lean_object* v_key_1328_; lean_object* v_value_1329_; lean_object* v_tail_1330_; uint8_t v___x_1331_; 
v_key_1328_ = lean_ctor_get(v_x_1326_, 0);
v_value_1329_ = lean_ctor_get(v_x_1326_, 1);
v_tail_1330_ = lean_ctor_get(v_x_1326_, 2);
v___x_1331_ = lean_name_eq(v_key_1328_, v_a_1325_);
if (v___x_1331_ == 0)
{
v_x_1326_ = v_tail_1330_;
goto _start;
}
else
{
lean_object* v___x_1333_; 
lean_inc(v_value_1329_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_value_1329_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1334_, v_x_1335_);
lean_dec(v_x_1335_);
lean_dec(v_a_1334_);
return v_res_1336_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1337_; uint64_t v___x_1338_; 
v___x_1337_ = lean_unsigned_to_nat(1723u);
v___x_1338_ = lean_uint64_of_nat(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_buckets_1341_; lean_object* v___x_1342_; uint64_t v___y_1344_; 
v_buckets_1341_ = lean_ctor_get(v_m_1339_, 1);
v___x_1342_ = lean_array_get_size(v_buckets_1341_);
if (lean_obj_tag(v_a_1340_) == 0)
{
uint64_t v___x_1358_; 
v___x_1358_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1344_ = v___x_1358_;
goto v___jp_1343_;
}
else
{
uint64_t v_hash_1359_; 
v_hash_1359_ = lean_ctor_get_uint64(v_a_1340_, sizeof(void*)*2);
v___y_1344_ = v_hash_1359_;
goto v___jp_1343_;
}
v___jp_1343_:
{
uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v_fold_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1345_ = 32ULL;
v___x_1346_ = lean_uint64_shift_right(v___y_1344_, v___x_1345_);
v_fold_1347_ = lean_uint64_xor(v___y_1344_, v___x_1346_);
v___x_1348_ = 16ULL;
v___x_1349_ = lean_uint64_shift_right(v_fold_1347_, v___x_1348_);
v___x_1350_ = lean_uint64_xor(v_fold_1347_, v___x_1349_);
v___x_1351_ = lean_uint64_to_usize(v___x_1350_);
v___x_1352_ = lean_usize_of_nat(v___x_1342_);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_sub(v___x_1352_, v___x_1353_);
v___x_1355_ = lean_usize_land(v___x_1351_, v___x_1354_);
v___x_1356_ = lean_array_uget_borrowed(v_buckets_1341_, v___x_1355_);
v___x_1357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1340_, v___x_1356_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_m_1360_);
return v_res_1362_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1366_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1367_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1366_, v___x_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1370_, uint8_t v_isMeta_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v_env_1379_; lean_object* v___y_1381_; lean_object* v___x_1394_; 
v___x_1375_ = lean_st_ref_get(v___y_1373_);
v_env_1379_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1379_);
lean_dec(v___x_1375_);
v___x_1394_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1379_, v_declName_1370_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_dec_ref(v_env_1379_);
lean_dec(v_declName_1370_);
goto v___jp_1376_;
}
else
{
lean_object* v_val_1395_; lean_object* v___x_1396_; lean_object* v_modules_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = l_Lean_Environment_header(v_env_1379_);
v_modules_1397_ = lean_ctor_get(v___x_1396_, 3);
lean_inc_ref(v_modules_1397_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = lean_array_get_size(v_modules_1397_);
v___x_1399_ = lean_nat_dec_lt(v_val_1395_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec_ref(v_modules_1397_);
lean_dec(v_val_1395_);
lean_dec_ref(v_env_1379_);
lean_dec(v_declName_1370_);
goto v___jp_1376_;
}
else
{
lean_object* v___x_1400_; lean_object* v_env_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___y_1405_; 
v___x_1400_ = lean_st_ref_get(v___y_1373_);
v_env_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc_ref(v_env_1401_);
lean_dec(v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1403_ = lean_array_fget(v_modules_1397_, v_val_1395_);
lean_dec(v_val_1395_);
lean_dec_ref(v_modules_1397_);
if (v_isMeta_1371_ == 0)
{
lean_dec_ref(v_env_1401_);
v___y_1405_ = v_isMeta_1371_;
goto v___jp_1404_;
}
else
{
uint8_t v___x_1416_; 
lean_inc(v_declName_1370_);
v___x_1416_ = l_Lean_isMarkedMeta(v_env_1401_, v_declName_1370_);
if (v___x_1416_ == 0)
{
v___y_1405_ = v_isMeta_1371_;
goto v___jp_1404_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
v___y_1405_ = v___x_1417_;
goto v___jp_1404_;
}
}
v___jp_1404_:
{
lean_object* v_toImport_1406_; lean_object* v_module_1407_; lean_object* v___x_1408_; 
v_toImport_1406_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_toImport_1406_);
lean_dec(v___x_1403_);
v_module_1407_ = lean_ctor_get(v_toImport_1406_, 0);
lean_inc(v_module_1407_);
lean_dec_ref(v_toImport_1406_);
lean_inc(v_declName_1370_);
v___x_1408_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1407_, v___y_1405_, v_declName_1370_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v___x_1408_);
v___x_1409_ = l_Lean_indirectModUseExt;
v___x_1410_ = lean_box(1);
v___x_1411_ = lean_box(0);
lean_inc_ref(v_env_1379_);
v___x_1412_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1402_, v___x_1409_, v_env_1379_, v___x_1410_, v___x_1411_);
v___x_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1412_, v_declName_1370_);
lean_dec(v___x_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1381_ = v___x_1414_;
goto v___jp_1380_;
}
else
{
lean_object* v_val_1415_; 
v_val_1415_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1415_);
lean_dec_ref(v___x_1413_);
v___y_1381_ = v_val_1415_;
goto v___jp_1380_;
}
}
else
{
lean_dec_ref(v_env_1379_);
lean_dec(v_declName_1370_);
return v___x_1408_;
}
}
}
}
v___jp_1376_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
v___jp_1380_:
{
lean_object* v___x_1382_; size_t v_sz_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_box(0);
v_sz_1383_ = lean_array_size(v___y_1381_);
v___x_1384_ = ((size_t)0ULL);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1379_, v_declName_1370_, v___y_1381_, v_sz_1383_, v___x_1384_, v___x_1382_, v___y_1372_, v___y_1373_);
lean_dec_ref(v___y_1381_);
lean_dec_ref(v_env_1379_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1382_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1382_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1418_, lean_object* v_isMeta_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v_isMeta_boxed_1423_; lean_object* v_res_1424_; 
v_isMeta_boxed_1423_ = lean_unbox(v_isMeta_1419_);
v_res_1424_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1418_, v_isMeta_boxed_1423_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1425_, uint8_t v_x_1426_, lean_object* v_stx_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
lean_inc(v_stx_1427_);
v___x_1431_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1425_, v_stx_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1484_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1484_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1484_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v_env_1437_; uint8_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1436_ = lean_st_ref_get(v___y_1429_);
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = 1;
lean_inc(v_a_1432_);
v___x_1439_ = l_Lean_Environment_contains(v_env_1437_, v_a_1432_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; 
lean_dec(v_stx_1427_);
if (v_isShared_1435_ == 0)
{
v___x_1441_ = v___x_1434_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1432_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
uint8_t v___x_1443_; lean_object* v___x_1444_; 
lean_del_object(v___x_1434_);
v___x_1443_ = 0;
lean_inc(v_a_1432_);
v___x_1444_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1432_, v___x_1443_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1444_, 0);
lean_dec(v_unused_1475_);
v___x_1446_ = v___x_1444_;
v_isShared_1447_ = v_isSharedCheck_1474_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v___x_1444_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1474_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v_infoState_1449_; uint8_t v_enabled_1450_; 
v___x_1448_ = lean_st_ref_get(v___y_1429_);
v_infoState_1449_ = lean_ctor_get(v___x_1448_, 7);
lean_inc_ref(v_infoState_1449_);
lean_dec(v___x_1448_);
v_enabled_1450_ = lean_ctor_get_uint8(v_infoState_1449_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1449_);
if (v_enabled_1450_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_stx_1427_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_a_1432_);
v___x_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1432_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_del_object(v___x_1446_);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1454_);
lean_dec(v_stx_1427_);
v___x_1456_ = lean_box(0);
lean_inc(v_a_1432_);
v___x_1457_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1455_, v_a_1432_, v___x_1456_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1457_, 0);
lean_dec(v_unused_1465_);
v___x_1459_ = v___x_1457_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1457_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v_a_1432_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1432_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1432_);
v_a_1466_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1457_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1457_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1432_);
lean_dec(v_stx_1427_);
v_a_1476_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1444_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1444_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1427_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1485_, lean_object* v_x_1486_, lean_object* v_stx_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_x_7288__boxed_1491_; lean_object* v_res_1492_; 
v_x_7288__boxed_1491_ = lean_unbox(v_x_1486_);
v_res_1492_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1485_, v_x_7288__boxed_1491_, v_stx_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1495_, lean_object* v_attrName_1496_, lean_object* v_parserNamespace_1497_, lean_object* v_typeName_1498_, lean_object* v_kind_1499_, lean_object* v_attrDeclName_1500_){
_start:
{
lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___f_1502_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1503_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1503_, 0, v_parserNamespace_1497_);
v___x_1504_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1505_ = lean_string_append(v_kind_1499_, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1506_, 0, v_attrBuiltinName_1495_);
lean_ctor_set(v___x_1506_, 1, v_attrName_1496_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
lean_ctor_set(v___x_1506_, 3, v_typeName_1498_);
lean_ctor_set(v___x_1506_, 4, v___f_1503_);
lean_ctor_set(v___x_1506_, 5, v___f_1502_);
v___x_1507_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1506_, v_attrDeclName_1500_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1508_, lean_object* v_attrName_1509_, lean_object* v_parserNamespace_1510_, lean_object* v_typeName_1511_, lean_object* v_kind_1512_, lean_object* v_attrDeclName_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1508_, v_attrName_1509_, v_parserNamespace_1510_, v_typeName_1511_, v_kind_1512_, v_attrDeclName_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1516_, lean_object* v_attrBuiltinName_1517_, lean_object* v_attrName_1518_, lean_object* v_parserNamespace_1519_, lean_object* v_typeName_1520_, lean_object* v_kind_1521_, lean_object* v_attrDeclName_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1517_, v_attrName_1518_, v_parserNamespace_1519_, v_typeName_1520_, v_kind_1521_, v_attrDeclName_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1525_, lean_object* v_attrBuiltinName_1526_, lean_object* v_attrName_1527_, lean_object* v_parserNamespace_1528_, lean_object* v_typeName_1529_, lean_object* v_kind_1530_, lean_object* v_attrDeclName_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1525_, v_attrBuiltinName_1526_, v_attrName_1527_, v_parserNamespace_1528_, v_typeName_1529_, v_kind_1530_, v_attrDeclName_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1534_, v___y_1535_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1544_, lean_object* v_m_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1545_, v_a_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1548_, v_m_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_m_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12(lean_object* v_t_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(v_t_1552_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___boxed(lean_object* v_t_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12(v_t_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
uint8_t v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1566_, v_x_1567_, v_x_1568_);
lean_dec_ref(v_x_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1571_, lean_object* v_a_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1572_, v_x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1575_, lean_object* v_a_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6(v_00_u03b2_1575_, v_a_1576_, v_x_1577_);
lean_dec(v_x_1577_);
lean_dec(v_a_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1579_, lean_object* v_x_1580_, size_t v_x_1581_, lean_object* v_x_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1580_, v_x_1581_, v_x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
size_t v_x_7469__boxed_1588_; uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_x_7469__boxed_1588_ = lean_unbox_usize(v_x_1586_);
lean_dec(v_x_1586_);
v_res_1589_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1584_, v_x_1585_, v_x_7469__boxed_1588_, v_x_1587_);
lean_dec_ref(v_x_1587_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_1591_, lean_object* v_constName_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_constName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11(v_00_u03b1_1597_, v_constName_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1603_, lean_object* v_keys_1604_, lean_object* v_vals_1605_, lean_object* v_heq_1606_, lean_object* v_i_1607_, lean_object* v_k_1608_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_1604_, v_i_1607_, v_k_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1610_, lean_object* v_keys_1611_, lean_object* v_vals_1612_, lean_object* v_heq_1613_, lean_object* v_i_1614_, lean_object* v_k_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10(v_00_u03b2_1610_, v_keys_1611_, v_vals_1612_, v_heq_1613_, v_i_1614_, v_k_1615_);
lean_dec_ref(v_k_1615_);
lean_dec_ref(v_vals_1612_);
lean_dec_ref(v_keys_1611_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15(lean_object* v_00_u03b1_1618_, lean_object* v_ref_1619_, lean_object* v_constName_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_1619_, v_constName_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_ref_1626_, lean_object* v_constName_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15(v_00_u03b1_1625_, v_ref_1626_, v_constName_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v_ref_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17(lean_object* v_00_u03b1_1632_, lean_object* v_ref_1633_, lean_object* v_msg_1634_, lean_object* v_declHint_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_1633_, v_msg_1634_, v_declHint_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___boxed(lean_object* v_00_u03b1_1640_, lean_object* v_ref_1641_, lean_object* v_msg_1642_, lean_object* v_declHint_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17(v_00_u03b1_1640_, v_ref_1641_, v_msg_1642_, v_declHint_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_ref_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_1648_, lean_object* v_declHint_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_1648_, v_declHint_1649_, v___y_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_1654_, lean_object* v_declHint_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19(v_msg_1654_, v_declHint_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_1660_, lean_object* v_ref_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_1661_, v_msg_1662_, v___y_1663_, v___y_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_ref_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19(v_00_u03b1_1667_, v_ref_1668_, v_msg_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v_ref_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1686_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1687_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1688_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1689_ = lean_box(0);
v___x_1690_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1691_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1686_, v___x_1688_, v___x_1689_, v___x_1690_, v___x_1687_, v_ref_1684_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1702_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1708_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1709_ = l_Lean_addBuiltinDocString(v___x_1707_, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1739_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1740_ = l_Lean_addBuiltinDeclarationRanges(v___x_1738_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1743_, lean_object* v_a_1744_, lean_object* v_____r_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_declName_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1759_; 
v_declName_1748_ = lean_ctor_get(v_toOLeanEntry_1743_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_toOLeanEntry_1743_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_toOLeanEntry_1743_, 0);
lean_dec(v_unused_1760_);
v___x_1750_ = v_toOLeanEntry_1743_;
v_isShared_1751_ = v_isSharedCheck_1759_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_declName_1748_);
lean_dec(v_toOLeanEntry_1743_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1759_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1744_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1752_);
lean_ctor_set(v___x_1750_, 0, v_declName_1748_);
v___x_1754_ = v___x_1750_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_declName_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___y_1747_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1761_, lean_object* v_a_1762_, lean_object* v_____r_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1761_, v_a_1762_, v_____r_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1770_, lean_object* v_as_x27_1771_, lean_object* v_b_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
if (lean_obj_tag(v_as_x27_1771_) == 0)
{
lean_object* v___x_1775_; 
lean_dec(v_stx_1770_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_b_1772_);
lean_ctor_set(v___x_1775_, 1, v___y_1774_);
return v___x_1775_;
}
else
{
lean_object* v_head_1776_; lean_object* v_tail_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1855_; 
lean_dec_ref(v_b_1772_);
v_head_1776_ = lean_ctor_get(v_as_x27_1771_, 0);
v_tail_1777_ = lean_ctor_get(v_as_x27_1771_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_as_x27_1771_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1779_ = v_as_x27_1771_;
v_isShared_1780_ = v_isSharedCheck_1855_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_tail_1777_);
lean_inc(v_head_1776_);
lean_dec(v_as_x27_1771_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1855_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_toOLeanEntry_1781_; uint8_t v_isBuiltin_1782_; lean_object* v_value_1783_; lean_object* v_macroScope_1784_; lean_object* v_traceMsgs_1785_; lean_object* v_expandedMacroDecls_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1854_; 
v_toOLeanEntry_1781_ = lean_ctor_get(v_head_1776_, 0);
lean_inc_ref(v_toOLeanEntry_1781_);
v_isBuiltin_1782_ = lean_ctor_get_uint8(v_head_1776_, sizeof(void*)*2);
v_value_1783_ = lean_ctor_get(v_head_1776_, 1);
lean_inc(v_value_1783_);
lean_dec(v_head_1776_);
v_macroScope_1784_ = lean_ctor_get(v___y_1774_, 0);
v_traceMsgs_1785_ = lean_ctor_get(v___y_1774_, 1);
v_expandedMacroDecls_1786_ = lean_ctor_get(v___y_1774_, 2);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1774_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1788_ = v___y_1774_;
v_isShared_1789_ = v_isSharedCheck_1854_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_expandedMacroDecls_1786_);
lean_inc(v_traceMsgs_1785_);
lean_inc(v_macroScope_1784_);
lean_dec(v___y_1774_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1854_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_methods_1790_; lean_object* v_quotContext_1791_; lean_object* v_currRecDepth_1792_; lean_object* v_maxRecDepth_1793_; lean_object* v_ref_1794_; lean_object* v___x_1795_; lean_object* v_a_1797_; lean_object* v_a_1798_; lean_object* v___x_1802_; lean_object* v_a_1804_; lean_object* v_a_1805_; lean_object* v___y_1819_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v_methods_1790_ = lean_ctor_get(v___y_1773_, 0);
v_quotContext_1791_ = lean_ctor_get(v___y_1773_, 1);
v_currRecDepth_1792_ = lean_ctor_get(v___y_1773_, 3);
v_maxRecDepth_1793_ = lean_ctor_get(v___y_1773_, 4);
v_ref_1794_ = lean_ctor_get(v___y_1773_, 5);
v___x_1795_ = lean_box(0);
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_macroScope_1784_, v___x_1825_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1826_);
v___x_1828_ = v___x_1788_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_traceMsgs_1785_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_expandedMacroDecls_1786_);
v___x_1828_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1827_;
}
v___jp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1797_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1795_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_a_1798_);
return v___x_1801_;
}
v___jp_1803_:
{
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_dec_ref(v_toOLeanEntry_1781_);
v_as_x27_1771_ = v_tail_1777_;
v_b_1772_ = v___x_1802_;
v___y_1774_ = v_a_1805_;
goto _start;
}
else
{
lean_object* v_declName_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_tail_1777_);
lean_dec(v_stx_1770_);
v_declName_1807_ = lean_ctor_get(v_toOLeanEntry_1781_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_toOLeanEntry_1781_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v_toOLeanEntry_1781_, 0);
lean_dec(v_unused_1817_);
v___x_1809_ = v_toOLeanEntry_1781_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_declName_1807_);
lean_dec(v_toOLeanEntry_1781_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1804_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1811_);
lean_ctor_set(v___x_1809_, 0, v_declName_1807_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_declName_1807_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
v_a_1797_ = v___x_1814_;
v_a_1798_ = v_a_1805_;
goto v___jp_1796_;
}
}
}
}
v___jp_1818_:
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___y_1819_, 0);
if (lean_obj_tag(v_a_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_a_1822_; 
lean_inc_ref(v_a_1820_);
lean_dec(v_tail_1777_);
lean_dec(v_stx_1770_);
v_a_1821_ = lean_ctor_get(v___y_1819_, 1);
lean_inc(v_a_1821_);
lean_dec_ref(v___y_1819_);
v_a_1822_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v_a_1820_);
v_a_1797_ = v_a_1822_;
v_a_1798_ = v_a_1821_;
goto v___jp_1796_;
}
else
{
lean_object* v_a_1823_; 
v_a_1823_ = lean_ctor_get(v___y_1819_, 1);
lean_inc(v_a_1823_);
lean_dec_ref(v___y_1819_);
v_as_x27_1771_ = v_tail_1777_;
v_b_1772_ = v___x_1802_;
v___y_1774_ = v_a_1823_;
goto _start;
}
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_inc(v_ref_1794_);
lean_inc(v_maxRecDepth_1793_);
lean_inc(v_currRecDepth_1792_);
lean_inc(v_quotContext_1791_);
lean_inc(v_methods_1790_);
v___x_1829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1829_, 0, v_methods_1790_);
lean_ctor_set(v___x_1829_, 1, v_quotContext_1791_);
lean_ctor_set(v___x_1829_, 2, v_macroScope_1784_);
lean_ctor_set(v___x_1829_, 3, v_currRecDepth_1792_);
lean_ctor_set(v___x_1829_, 4, v_maxRecDepth_1793_);
lean_ctor_set(v___x_1829_, 5, v_ref_1794_);
lean_inc(v_stx_1770_);
v___x_1830_ = lean_apply_3(v_value_1783_, v_stx_1770_, v___x_1829_, v___x_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
if (v_isBuiltin_1782_ == 0)
{
lean_object* v_a_1831_; lean_object* v_a_1832_; lean_object* v_macroScope_1833_; lean_object* v_traceMsgs_1834_; lean_object* v_expandedMacroDecls_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1847_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_a_1831_);
v_a_1832_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1830_);
v_macroScope_1833_ = lean_ctor_get(v_a_1831_, 0);
v_traceMsgs_1834_ = lean_ctor_get(v_a_1831_, 1);
v_expandedMacroDecls_1835_ = lean_ctor_get(v_a_1831_, 2);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_a_1831_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1837_ = v_a_1831_;
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_expandedMacroDecls_1835_);
lean_inc(v_traceMsgs_1834_);
lean_inc(v_macroScope_1833_);
lean_dec(v_a_1831_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1847_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_declName_1839_; lean_object* v___x_1841_; 
v_declName_1839_ = lean_ctor_get(v_toOLeanEntry_1781_, 1);
lean_inc(v_declName_1839_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v_expandedMacroDecls_1835_);
lean_ctor_set(v___x_1779_, 0, v_declName_1839_);
v___x_1841_ = v___x_1779_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_declName_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_expandedMacroDecls_1835_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 2, v___x_1841_);
v___x_1843_ = v___x_1837_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_macroScope_1833_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_traceMsgs_1834_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1781_, v_a_1832_, v___x_1795_, v___y_1773_, v___x_1843_);
v___y_1819_ = v___x_1844_;
goto v___jp_1818_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v_a_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1779_);
v_a_1848_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1848_);
v_a_1849_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1830_);
v___x_1850_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1781_, v_a_1848_, v___x_1795_, v___y_1773_, v_a_1849_);
v___y_1819_ = v___x_1850_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v_a_1852_; 
lean_del_object(v___x_1779_);
v_a_1851_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1851_);
v_a_1852_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1830_);
v_a_1804_ = v_a_1851_;
v_a_1805_ = v_a_1852_;
goto v___jp_1803_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1856_, lean_object* v_as_x27_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1856_, v_as_x27_1857_, v_b_1858_, v___y_1859_, v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1862_, lean_object* v_stx_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v_fst_1873_; 
v___x_1866_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1863_);
v___x_1867_ = l_Lean_Syntax_getKind(v_stx_1863_);
v___x_1868_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1866_, v_env_1862_, v___x_1867_);
lean_dec(v___x_1867_);
v___x_1869_ = lean_box(0);
v___x_1870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1871_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1863_, v___x_1868_, v___x_1870_, v_a_1864_, v_a_1865_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
v_fst_1873_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_fst_1873_);
lean_dec(v_a_1872_);
if (lean_obj_tag(v_fst_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1882_);
v___x_1876_ = v___x_1871_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1871_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1869_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_a_1883_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1892_);
v___x_1885_ = v___x_1871_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1871_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_val_1887_; lean_object* v___x_1889_; 
v_val_1887_ = lean_ctor_get(v_fst_1873_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v_fst_1873_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_val_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_val_1887_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_a_1883_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1893_, lean_object* v_stx_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1893_, v_stx_1894_, v_a_1895_, v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1898_, lean_object* v_as_1899_, lean_object* v_as_x27_1900_, lean_object* v_b_1901_, lean_object* v_a_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1898_, v_as_x27_1900_, v_b_1901_, v___y_1903_, v___y_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1906_, lean_object* v_as_1907_, lean_object* v_as_x27_1908_, lean_object* v_b_1909_, lean_object* v_a_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1906_, v_as_1907_, v_as_x27_1908_, v_b_1909_, v_a_1910_, v___y_1911_, v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v_as_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1914_, lean_object* v_inst_1915_, lean_object* v_s_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_apply_1(v_setNextMacroScope_1914_, v_s_1916_);
v___x_1918_ = lean_apply_2(v_inst_1915_, lean_box(0), v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_inst_1921_){
_start:
{
lean_object* v_getNextMacroScope_1922_; lean_object* v_setNextMacroScope_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1932_; 
v_getNextMacroScope_1922_ = lean_ctor_get(v_inst_1921_, 1);
v_setNextMacroScope_1923_ = lean_ctor_get(v_inst_1921_, 2);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_inst_1921_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_inst_1921_, 0);
lean_dec(v_unused_1933_);
v___x_1925_ = v_inst_1921_;
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_setNextMacroScope_1923_);
lean_inc(v_getNextMacroScope_1922_);
lean_dec(v_inst_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_inc(v_inst_1919_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1927_, 0, v_setNextMacroScope_1923_);
lean_closure_set(v___f_1927_, 1, v_inst_1919_);
v___x_1928_ = lean_apply_2(v_inst_1919_, lean_box(0), v_getNextMacroScope_1922_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 2, v___f_1927_);
lean_ctor_set(v___x_1925_, 1, v___x_1928_);
lean_ctor_set(v___x_1925_, 0, v_inst_1920_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_inst_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v___f_1927_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1934_, lean_object* v_n_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_){
_start:
{
lean_object* v_getNextMacroScope_1939_; lean_object* v_setNextMacroScope_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1949_; 
v_getNextMacroScope_1939_ = lean_ctor_get(v_inst_1938_, 1);
v_setNextMacroScope_1940_ = lean_ctor_get(v_inst_1938_, 2);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_inst_1938_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_inst_1938_, 0);
lean_dec(v_unused_1950_);
v___x_1942_ = v_inst_1938_;
v_isShared_1943_ = v_isSharedCheck_1949_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_setNextMacroScope_1940_);
lean_inc(v_getNextMacroScope_1939_);
lean_dec(v_inst_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1949_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___f_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_inc(v_inst_1936_);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1944_, 0, v_setNextMacroScope_1940_);
lean_closure_set(v___f_1944_, 1, v_inst_1936_);
v___x_1945_ = lean_apply_2(v_inst_1936_, lean_box(0), v_getNextMacroScope_1939_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 2, v___f_1944_);
lean_ctor_set(v___x_1942_, 1, v___x_1945_);
lean_ctor_set(v___x_1942_, 0, v_inst_1937_);
v___x_1947_ = v___x_1942_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_inst_1937_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v___f_1944_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1951_, lean_object* v_snd_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_toMonadRef_1955_, lean_object* v_inst_1956_, lean_object* v_fst_1957_, uint8_t v_____do__lift_1958_){
_start:
{
if (v_____do__lift_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec(v_fst_1957_);
lean_dec(v_inst_1956_);
lean_dec_ref(v_toMonadRef_1955_);
lean_dec_ref(v_inst_1954_);
lean_dec_ref(v_inst_1953_);
lean_dec_ref(v_snd_1952_);
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_apply_2(v_toPure_1951_, lean_box(0), v___x_1959_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v_toPure_1951_);
v___x_1961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_snd_1952_);
v___x_1962_ = l_Lean_MessageData_ofFormat(v___x_1961_);
v___x_1963_ = l_Lean_addTrace___redArg(v_inst_1953_, v_inst_1954_, v_toMonadRef_1955_, v_inst_1956_, v_fst_1957_, v___x_1962_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1964_, lean_object* v_snd_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_toMonadRef_1968_, lean_object* v_inst_1969_, lean_object* v_fst_1970_, lean_object* v_____do__lift_1971_){
_start:
{
uint8_t v_____do__lift_1350__boxed_1972_; lean_object* v_res_1973_; 
v_____do__lift_1350__boxed_1972_ = lean_unbox(v_____do__lift_1971_);
v_res_1973_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1964_, v_snd_1965_, v_inst_1966_, v_inst_1967_, v_toMonadRef_1968_, v_inst_1969_, v_fst_1970_, v_____do__lift_1350__boxed_1972_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_toMonadRef_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_toBind_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_fst_1982_ = lean_ctor_get(v_x_1981_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v_x_1981_, 1);
lean_inc(v_snd_1983_);
lean_dec_ref(v_x_1981_);
lean_inc(v_fst_1982_);
lean_inc_ref(v_inst_1976_);
lean_inc_ref(v_inst_1975_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1984_, 0, v_toPure_1974_);
lean_closure_set(v___f_1984_, 1, v_snd_1983_);
lean_closure_set(v___f_1984_, 2, v_inst_1975_);
lean_closure_set(v___f_1984_, 3, v_inst_1976_);
lean_closure_set(v___f_1984_, 4, v_toMonadRef_1977_);
lean_closure_set(v___f_1984_, 5, v_inst_1978_);
lean_closure_set(v___f_1984_, 6, v_fst_1982_);
v___x_1985_ = l_Lean_isTracingEnabledFor___redArg(v_inst_1975_, v_inst_1976_, v_inst_1979_, v_fst_1982_);
v___x_1986_ = lean_apply_4(v_toBind_1980_, lean_box(0), lean_box(0), v___x_1985_, v___f_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_env_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v_stx_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1987_, v_stx_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
if (lean_obj_tag(v_a_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v___x_1989_);
lean_dec_ref(v___x_1988_);
v_a_1995_ = lean_ctor_get(v___x_1993_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v___x_1993_, 0);
lean_dec(v_unused_2004_);
v___x_1997_ = v___x_1993_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1993_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_a_1995_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_val_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2035_; 
v_val_2005_ = lean_ctor_get(v_a_1994_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2007_ = v_a_1994_;
v_isShared_2008_ = v_isSharedCheck_2035_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_val_2005_);
lean_dec(v_a_1994_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2035_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_snd_2009_; 
v_snd_2009_ = lean_ctor_get(v_val_2005_, 1);
lean_inc(v_snd_2009_);
lean_dec(v_val_2005_);
if (lean_obj_tag(v_snd_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_2007_);
v_a_2010_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_1993_);
v_a_2011_ = lean_ctor_get(v_snd_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_snd_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2013_ = v_snd_2009_;
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v_snd_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_1129__overap_2017_; lean_object* v___x_2018_; 
v___x_1129__overap_2017_ = l_liftExcept___redArg(v___x_1988_, v___x_1989_, v___x_2016_);
lean_inc_ref(v___y_1991_);
v___x_2018_ = lean_apply_2(v___x_1129__overap_2017_, v___y_1991_, v_a_2010_);
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2034_; 
v_a_2021_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_1993_);
v_a_2022_ = lean_ctor_get(v_snd_2009_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_snd_2009_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2024_ = v_snd_2009_;
v_isShared_2025_ = v_isSharedCheck_2034_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v_snd_2009_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2034_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v_a_2022_);
v___x_2027_ = v___x_2007_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_1133__overap_2030_; lean_object* v___x_2031_; 
v___x_1133__overap_2030_ = l_liftExcept___redArg(v___x_1988_, v___x_1989_, v___x_2029_);
lean_inc_ref(v___y_1991_);
v___x_2031_ = lean_apply_2(v___x_1133__overap_2030_, v___y_1991_, v_a_2021_);
return v___x_2031_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v___x_1989_);
lean_dec_ref(v___x_1988_);
v_a_2036_ = lean_ctor_get(v___x_1993_, 0);
v_a_2037_ = lean_ctor_get(v___x_1993_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1993_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_inc(v_a_2036_);
lean_dec(v___x_1993_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object* v_env_2045_, lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v_stx_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_env_2045_, v___x_2046_, v___x_2047_, v_stx_2048_, v___y_2049_, v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_env_2052_, lean_object* v_declName_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v___x_2056_; lean_object* v_env_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; uint8_t v___x_2060_; 
v___x_2056_ = 0;
v_env_2057_ = l_Lean_Environment_setExporting(v_env_2052_, v___x_2056_);
lean_inc(v_declName_2053_);
v___x_2058_ = l_Lean_mkPrivateName(v_env_2057_, v_declName_2053_);
v___x_2059_ = 1;
lean_inc_ref(v_env_2057_);
v___x_2060_ = l_Lean_Environment_contains(v_env_2057_, v___x_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = l_Lean_privateToUserName(v_declName_2053_);
v___x_2062_ = l_Lean_Environment_contains(v_env_2057_, v___x_2061_, v___x_2059_);
v___x_2063_ = lean_box(v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___y_2055_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v_env_2057_);
lean_dec(v_declName_2053_);
v___x_2065_ = lean_box(v___x_2060_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___y_2055_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3___boxed(lean_object* v_env_2067_, lean_object* v_declName_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Elab_liftMacroM___redArg___lam__3(v_env_2067_, v_declName_2068_, v___y_2069_, v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_2072_, lean_object* v_currNamespace_2073_, lean_object* v_openDecls_2074_, lean_object* v_n_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = l_Lean_ResolveName_resolveNamespace(v_env_2072_, v_currNamespace_2073_, v_openDecls_2074_, v_n_2075_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2080_, lean_object* v_currNamespace_2081_, lean_object* v_openDecls_2082_, lean_object* v_n_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2080_, v_currNamespace_2081_, v_openDecls_2082_, v_n_2083_, v___y_2084_, v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2087_, lean_object* v_opts_2088_, lean_object* v_currNamespace_2089_, lean_object* v_openDecls_2090_, lean_object* v_n_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = l_Lean_ResolveName_resolveGlobalName(v_env_2087_, v_opts_2088_, v_currNamespace_2089_, v_openDecls_2090_, v_n_2091_);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___y_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2096_, lean_object* v_opts_2097_, lean_object* v_currNamespace_2098_, lean_object* v_openDecls_2099_, lean_object* v_n_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2096_, v_opts_2097_, v_currNamespace_2098_, v_openDecls_2099_, v_n_2100_, v___y_2101_, v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_opts_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_toPure_2104_, lean_object* v_a_2105_, lean_object* v_____r_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_apply_2(v_toPure_2104_, lean_box(0), v_a_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_traceMsgs_2108_, lean_object* v_inst_2109_, lean_object* v___f_2110_, lean_object* v_toBind_2111_, lean_object* v___f_2112_, lean_object* v_____r_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = l_List_reverse___redArg(v_traceMsgs_2108_);
v___x_2115_ = l_List_forM___redArg(v_inst_2109_, v___x_2114_, v___f_2110_);
v___x_2116_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2115_, v___f_2112_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_setNextMacroScope_2117_, lean_object* v_macroScope_2118_, lean_object* v_toBind_2119_, lean_object* v___f_2120_, lean_object* v_____s_2121_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_apply_1(v_setNextMacroScope_2117_, v_macroScope_2118_);
v___x_2123_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2122_, v___f_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v___x_2124_, lean_object* v_toPure_2125_, lean_object* v_____r_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2124_);
v___x_2128_ = lean_apply_2(v_toPure_2125_, lean_box(0), v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_toMonadRef_2133_, lean_object* v_inst_2134_, lean_object* v_toBind_2135_, lean_object* v___f_2136_, lean_object* v_a_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = 1;
v___x_2141_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2129_, v_inst_2130_, v_inst_2131_, v_inst_2132_, v_toMonadRef_2133_, v_inst_2134_, v_a_2137_, v___x_2140_);
v___x_2142_ = lean_apply_4(v_toBind_2135_, lean_box(0), lean_box(0), v___x_2141_, v___f_2136_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v_methods_2144_, lean_object* v_____do__lift_2145_, lean_object* v_____do__lift_2146_, lean_object* v_____do__lift_2147_, lean_object* v_____do__lift_2148_, lean_object* v_____do__lift_2149_, lean_object* v_x_2150_, lean_object* v_toPure_2151_, lean_object* v_inst_2152_, lean_object* v___f_2153_, lean_object* v_toBind_2154_, lean_object* v_setNextMacroScope_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_toMonadRef_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_toMonadExceptOf_2162_, lean_object* v_____do__lift_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2164_, 0, v_methods_2144_);
lean_ctor_set(v___x_2164_, 1, v_____do__lift_2145_);
lean_ctor_set(v___x_2164_, 2, v_____do__lift_2146_);
lean_ctor_set(v___x_2164_, 3, v_____do__lift_2147_);
lean_ctor_set(v___x_2164_, 4, v_____do__lift_2148_);
lean_ctor_set(v___x_2164_, 5, v_____do__lift_2149_);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2166_, 0, v_____do__lift_2163_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
lean_ctor_set(v___x_2166_, 2, v___x_2165_);
v___x_2167_ = lean_apply_2(v_x_2150_, v___x_2164_, v___x_2166_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v_a_2169_; lean_object* v_macroScope_2170_; lean_object* v_traceMsgs_2171_; lean_object* v_expandedMacroDecls_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v_toMonadExceptOf_2162_);
lean_dec_ref(v_inst_2161_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_a_2168_);
v_a_2169_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2167_);
v_macroScope_2170_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_macroScope_2170_);
v_traceMsgs_2171_ = lean_ctor_get(v_a_2168_, 1);
lean_inc(v_traceMsgs_2171_);
v_expandedMacroDecls_2172_ = lean_ctor_get(v_a_2168_, 2);
lean_inc(v_expandedMacroDecls_2172_);
lean_dec(v_a_2168_);
lean_inc(v_toPure_2151_);
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6), 3, 2);
lean_closure_set(v___f_2173_, 0, v_toPure_2151_);
lean_closure_set(v___f_2173_, 1, v_a_2169_);
lean_inc(v_toBind_2154_);
lean_inc_ref(v_inst_2152_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7), 6, 5);
lean_closure_set(v___f_2174_, 0, v_traceMsgs_2171_);
lean_closure_set(v___f_2174_, 1, v_inst_2152_);
lean_closure_set(v___f_2174_, 2, v___f_2153_);
lean_closure_set(v___f_2174_, 3, v_toBind_2154_);
lean_closure_set(v___f_2174_, 4, v___f_2173_);
lean_inc(v_toBind_2154_);
v___f_2175_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2175_, 0, v_setNextMacroScope_2155_);
lean_closure_set(v___f_2175_, 1, v_macroScope_2170_);
lean_closure_set(v___f_2175_, 2, v_toBind_2154_);
lean_closure_set(v___f_2175_, 3, v___f_2174_);
v___x_2176_ = lean_box(0);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_2177_, 0, v___x_2176_);
lean_closure_set(v___f_2177_, 1, v_toPure_2151_);
lean_inc(v_toBind_2154_);
lean_inc_ref(v_inst_2152_);
v___f_2178_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 11, 8);
lean_closure_set(v___f_2178_, 0, v_inst_2152_);
lean_closure_set(v___f_2178_, 1, v_inst_2156_);
lean_closure_set(v___f_2178_, 2, v_inst_2157_);
lean_closure_set(v___f_2178_, 3, v_inst_2158_);
lean_closure_set(v___f_2178_, 4, v_toMonadRef_2159_);
lean_closure_set(v___f_2178_, 5, v_inst_2160_);
lean_closure_set(v___f_2178_, 6, v_toBind_2154_);
lean_closure_set(v___f_2178_, 7, v___f_2177_);
v___x_2179_ = l_List_forIn_x27_loop___redArg(v_inst_2152_, v___f_2178_, v_expandedMacroDecls_2172_, v___x_2176_);
v___x_2180_ = lean_apply_4(v_toBind_2154_, lean_box(0), lean_box(0), v___x_2179_, v___f_2175_);
return v___x_2180_;
}
else
{
lean_object* v_a_2181_; 
lean_dec(v_inst_2160_);
lean_dec_ref(v_toMonadRef_2159_);
lean_dec(v_inst_2158_);
lean_dec_ref(v_inst_2157_);
lean_dec_ref(v_inst_2156_);
lean_dec(v_setNextMacroScope_2155_);
lean_dec(v_toBind_2154_);
lean_dec(v___f_2153_);
lean_dec(v_toPure_2151_);
v_a_2181_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v_a_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
lean_dec_ref(v_toMonadExceptOf_2162_);
v_a_2182_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_a_2182_);
v_a_2183_ = lean_ctor_get(v_a_2181_, 1);
lean_inc_ref(v_a_2183_);
lean_dec_ref(v_a_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__11___closed__0));
v___x_2185_ = lean_string_dec_eq(v_a_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2183_);
v___x_2187_ = l_Lean_MessageData_ofFormat(v___x_2186_);
v___x_2188_ = l_Lean_throwErrorAt___redArg(v_inst_2152_, v_inst_2161_, v_a_2182_, v___x_2187_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_a_2183_);
lean_dec_ref(v_inst_2152_);
v___x_2189_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2161_, v_a_2182_);
return v___x_2189_;
}
}
else
{
lean_object* v___x_2190_; 
lean_dec_ref(v_inst_2161_);
lean_dec_ref(v_inst_2152_);
v___x_2190_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2162_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_methods_2191_ = _args[0];
lean_object* v_____do__lift_2192_ = _args[1];
lean_object* v_____do__lift_2193_ = _args[2];
lean_object* v_____do__lift_2194_ = _args[3];
lean_object* v_____do__lift_2195_ = _args[4];
lean_object* v_____do__lift_2196_ = _args[5];
lean_object* v_x_2197_ = _args[6];
lean_object* v_toPure_2198_ = _args[7];
lean_object* v_inst_2199_ = _args[8];
lean_object* v___f_2200_ = _args[9];
lean_object* v_toBind_2201_ = _args[10];
lean_object* v_setNextMacroScope_2202_ = _args[11];
lean_object* v_inst_2203_ = _args[12];
lean_object* v_inst_2204_ = _args[13];
lean_object* v_inst_2205_ = _args[14];
lean_object* v_toMonadRef_2206_ = _args[15];
lean_object* v_inst_2207_ = _args[16];
lean_object* v_inst_2208_ = _args[17];
lean_object* v_toMonadExceptOf_2209_ = _args[18];
lean_object* v_____do__lift_2210_ = _args[19];
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Elab_liftMacroM___redArg___lam__11(v_methods_2191_, v_____do__lift_2192_, v_____do__lift_2193_, v_____do__lift_2194_, v_____do__lift_2195_, v_____do__lift_2196_, v_x_2197_, v_toPure_2198_, v_inst_2199_, v___f_2200_, v_toBind_2201_, v_setNextMacroScope_2202_, v_inst_2203_, v_inst_2204_, v_inst_2205_, v_toMonadRef_2206_, v_inst_2207_, v_inst_2208_, v_toMonadExceptOf_2209_, v_____do__lift_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_methods_2212_, lean_object* v_____do__lift_2213_, lean_object* v_____do__lift_2214_, lean_object* v_____do__lift_2215_, lean_object* v_____do__lift_2216_, lean_object* v_x_2217_, lean_object* v_toPure_2218_, lean_object* v_inst_2219_, lean_object* v___f_2220_, lean_object* v_toBind_2221_, lean_object* v_setNextMacroScope_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_toMonadRef_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_toMonadExceptOf_2229_, lean_object* v_getNextMacroScope_2230_, lean_object* v_____do__lift_2231_){
_start:
{
lean_object* v___f_2232_; lean_object* v___x_2233_; 
lean_inc(v_toBind_2221_);
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11___boxed), 20, 19);
lean_closure_set(v___f_2232_, 0, v_methods_2212_);
lean_closure_set(v___f_2232_, 1, v_____do__lift_2213_);
lean_closure_set(v___f_2232_, 2, v_____do__lift_2214_);
lean_closure_set(v___f_2232_, 3, v_____do__lift_2215_);
lean_closure_set(v___f_2232_, 4, v_____do__lift_2231_);
lean_closure_set(v___f_2232_, 5, v_____do__lift_2216_);
lean_closure_set(v___f_2232_, 6, v_x_2217_);
lean_closure_set(v___f_2232_, 7, v_toPure_2218_);
lean_closure_set(v___f_2232_, 8, v_inst_2219_);
lean_closure_set(v___f_2232_, 9, v___f_2220_);
lean_closure_set(v___f_2232_, 10, v_toBind_2221_);
lean_closure_set(v___f_2232_, 11, v_setNextMacroScope_2222_);
lean_closure_set(v___f_2232_, 12, v_inst_2223_);
lean_closure_set(v___f_2232_, 13, v_inst_2224_);
lean_closure_set(v___f_2232_, 14, v_inst_2225_);
lean_closure_set(v___f_2232_, 15, v_toMonadRef_2226_);
lean_closure_set(v___f_2232_, 16, v_inst_2227_);
lean_closure_set(v___f_2232_, 17, v_inst_2228_);
lean_closure_set(v___f_2232_, 18, v_toMonadExceptOf_2229_);
v___x_2233_ = lean_apply_4(v_toBind_2221_, lean_box(0), lean_box(0), v_getNextMacroScope_2230_, v___f_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_methods_2234_ = _args[0];
lean_object* v_____do__lift_2235_ = _args[1];
lean_object* v_____do__lift_2236_ = _args[2];
lean_object* v_____do__lift_2237_ = _args[3];
lean_object* v_____do__lift_2238_ = _args[4];
lean_object* v_x_2239_ = _args[5];
lean_object* v_toPure_2240_ = _args[6];
lean_object* v_inst_2241_ = _args[7];
lean_object* v___f_2242_ = _args[8];
lean_object* v_toBind_2243_ = _args[9];
lean_object* v_setNextMacroScope_2244_ = _args[10];
lean_object* v_inst_2245_ = _args[11];
lean_object* v_inst_2246_ = _args[12];
lean_object* v_inst_2247_ = _args[13];
lean_object* v_toMonadRef_2248_ = _args[14];
lean_object* v_inst_2249_ = _args[15];
lean_object* v_inst_2250_ = _args[16];
lean_object* v_toMonadExceptOf_2251_ = _args[17];
lean_object* v_getNextMacroScope_2252_ = _args[18];
lean_object* v_____do__lift_2253_ = _args[19];
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Elab_liftMacroM___redArg___lam__12(v_methods_2234_, v_____do__lift_2235_, v_____do__lift_2236_, v_____do__lift_2237_, v_____do__lift_2238_, v_x_2239_, v_toPure_2240_, v_inst_2241_, v___f_2242_, v_toBind_2243_, v_setNextMacroScope_2244_, v_inst_2245_, v_inst_2246_, v_inst_2247_, v_toMonadRef_2248_, v_inst_2249_, v_inst_2250_, v_toMonadExceptOf_2251_, v_getNextMacroScope_2252_, v_____do__lift_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2255_, lean_object* v_____do__lift_2256_, lean_object* v_____do__lift_2257_, lean_object* v_____do__lift_2258_, lean_object* v_x_2259_, lean_object* v_toPure_2260_, lean_object* v_inst_2261_, lean_object* v___f_2262_, lean_object* v_toBind_2263_, lean_object* v_setNextMacroScope_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_toMonadRef_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_toMonadExceptOf_2271_, lean_object* v_getNextMacroScope_2272_, lean_object* v_getMaxRecDepth_2273_, lean_object* v_____do__lift_2274_){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
lean_inc(v_toBind_2263_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12___boxed), 20, 19);
lean_closure_set(v___f_2275_, 0, v_methods_2255_);
lean_closure_set(v___f_2275_, 1, v_____do__lift_2256_);
lean_closure_set(v___f_2275_, 2, v_____do__lift_2257_);
lean_closure_set(v___f_2275_, 3, v_____do__lift_2274_);
lean_closure_set(v___f_2275_, 4, v_____do__lift_2258_);
lean_closure_set(v___f_2275_, 5, v_x_2259_);
lean_closure_set(v___f_2275_, 6, v_toPure_2260_);
lean_closure_set(v___f_2275_, 7, v_inst_2261_);
lean_closure_set(v___f_2275_, 8, v___f_2262_);
lean_closure_set(v___f_2275_, 9, v_toBind_2263_);
lean_closure_set(v___f_2275_, 10, v_setNextMacroScope_2264_);
lean_closure_set(v___f_2275_, 11, v_inst_2265_);
lean_closure_set(v___f_2275_, 12, v_inst_2266_);
lean_closure_set(v___f_2275_, 13, v_inst_2267_);
lean_closure_set(v___f_2275_, 14, v_toMonadRef_2268_);
lean_closure_set(v___f_2275_, 15, v_inst_2269_);
lean_closure_set(v___f_2275_, 16, v_inst_2270_);
lean_closure_set(v___f_2275_, 17, v_toMonadExceptOf_2271_);
lean_closure_set(v___f_2275_, 18, v_getNextMacroScope_2272_);
v___x_2276_ = lean_apply_4(v_toBind_2263_, lean_box(0), lean_box(0), v_getMaxRecDepth_2273_, v___f_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2277_ = _args[0];
lean_object* v_____do__lift_2278_ = _args[1];
lean_object* v_____do__lift_2279_ = _args[2];
lean_object* v_____do__lift_2280_ = _args[3];
lean_object* v_x_2281_ = _args[4];
lean_object* v_toPure_2282_ = _args[5];
lean_object* v_inst_2283_ = _args[6];
lean_object* v___f_2284_ = _args[7];
lean_object* v_toBind_2285_ = _args[8];
lean_object* v_setNextMacroScope_2286_ = _args[9];
lean_object* v_inst_2287_ = _args[10];
lean_object* v_inst_2288_ = _args[11];
lean_object* v_inst_2289_ = _args[12];
lean_object* v_toMonadRef_2290_ = _args[13];
lean_object* v_inst_2291_ = _args[14];
lean_object* v_inst_2292_ = _args[15];
lean_object* v_toMonadExceptOf_2293_ = _args[16];
lean_object* v_getNextMacroScope_2294_ = _args[17];
lean_object* v_getMaxRecDepth_2295_ = _args[18];
lean_object* v_____do__lift_2296_ = _args[19];
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2277_, v_____do__lift_2278_, v_____do__lift_2279_, v_____do__lift_2280_, v_x_2281_, v_toPure_2282_, v_inst_2283_, v___f_2284_, v_toBind_2285_, v_setNextMacroScope_2286_, v_inst_2287_, v_inst_2288_, v_inst_2289_, v_toMonadRef_2290_, v_inst_2291_, v_inst_2292_, v_toMonadExceptOf_2293_, v_getNextMacroScope_2294_, v_getMaxRecDepth_2295_, v_____do__lift_2296_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_inst_2298_, lean_object* v_methods_2299_, lean_object* v_____do__lift_2300_, lean_object* v_____do__lift_2301_, lean_object* v_x_2302_, lean_object* v_toPure_2303_, lean_object* v_inst_2304_, lean_object* v___f_2305_, lean_object* v_toBind_2306_, lean_object* v_setNextMacroScope_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_toMonadRef_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_toMonadExceptOf_2314_, lean_object* v_getNextMacroScope_2315_, lean_object* v_____do__lift_2316_){
_start:
{
lean_object* v_getRecDepth_2317_; lean_object* v_getMaxRecDepth_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_getRecDepth_2317_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc(v_getRecDepth_2317_);
v_getMaxRecDepth_2318_ = lean_ctor_get(v_inst_2298_, 2);
lean_inc(v_getMaxRecDepth_2318_);
lean_dec_ref(v_inst_2298_);
lean_inc(v_toBind_2306_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2319_, 0, v_methods_2299_);
lean_closure_set(v___f_2319_, 1, v_____do__lift_2316_);
lean_closure_set(v___f_2319_, 2, v_____do__lift_2300_);
lean_closure_set(v___f_2319_, 3, v_____do__lift_2301_);
lean_closure_set(v___f_2319_, 4, v_x_2302_);
lean_closure_set(v___f_2319_, 5, v_toPure_2303_);
lean_closure_set(v___f_2319_, 6, v_inst_2304_);
lean_closure_set(v___f_2319_, 7, v___f_2305_);
lean_closure_set(v___f_2319_, 8, v_toBind_2306_);
lean_closure_set(v___f_2319_, 9, v_setNextMacroScope_2307_);
lean_closure_set(v___f_2319_, 10, v_inst_2308_);
lean_closure_set(v___f_2319_, 11, v_inst_2309_);
lean_closure_set(v___f_2319_, 12, v_inst_2310_);
lean_closure_set(v___f_2319_, 13, v_toMonadRef_2311_);
lean_closure_set(v___f_2319_, 14, v_inst_2312_);
lean_closure_set(v___f_2319_, 15, v_inst_2313_);
lean_closure_set(v___f_2319_, 16, v_toMonadExceptOf_2314_);
lean_closure_set(v___f_2319_, 17, v_getNextMacroScope_2315_);
lean_closure_set(v___f_2319_, 18, v_getMaxRecDepth_2318_);
v___x_2320_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v_getRecDepth_2317_, v___f_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_inst_2321_ = _args[0];
lean_object* v_methods_2322_ = _args[1];
lean_object* v_____do__lift_2323_ = _args[2];
lean_object* v_____do__lift_2324_ = _args[3];
lean_object* v_x_2325_ = _args[4];
lean_object* v_toPure_2326_ = _args[5];
lean_object* v_inst_2327_ = _args[6];
lean_object* v___f_2328_ = _args[7];
lean_object* v_toBind_2329_ = _args[8];
lean_object* v_setNextMacroScope_2330_ = _args[9];
lean_object* v_inst_2331_ = _args[10];
lean_object* v_inst_2332_ = _args[11];
lean_object* v_inst_2333_ = _args[12];
lean_object* v_toMonadRef_2334_ = _args[13];
lean_object* v_inst_2335_ = _args[14];
lean_object* v_inst_2336_ = _args[15];
lean_object* v_toMonadExceptOf_2337_ = _args[16];
lean_object* v_getNextMacroScope_2338_ = _args[17];
lean_object* v_____do__lift_2339_ = _args[18];
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_inst_2321_, v_methods_2322_, v_____do__lift_2323_, v_____do__lift_2324_, v_x_2325_, v_toPure_2326_, v_inst_2327_, v___f_2328_, v_toBind_2329_, v_setNextMacroScope_2330_, v_inst_2331_, v_inst_2332_, v_inst_2333_, v_toMonadRef_2334_, v_inst_2335_, v_inst_2336_, v_toMonadExceptOf_2337_, v_getNextMacroScope_2338_, v_____do__lift_2339_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_inst_2341_, lean_object* v_methods_2342_, lean_object* v_____do__lift_2343_, lean_object* v_x_2344_, lean_object* v_toPure_2345_, lean_object* v_inst_2346_, lean_object* v___f_2347_, lean_object* v_toBind_2348_, lean_object* v_setNextMacroScope_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_toMonadRef_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_toMonadExceptOf_2356_, lean_object* v_getNextMacroScope_2357_, lean_object* v_getContext_2358_, lean_object* v_____do__lift_2359_){
_start:
{
lean_object* v___f_2360_; lean_object* v___x_2361_; 
lean_inc(v_toBind_2348_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 19, 18);
lean_closure_set(v___f_2360_, 0, v_inst_2341_);
lean_closure_set(v___f_2360_, 1, v_methods_2342_);
lean_closure_set(v___f_2360_, 2, v_____do__lift_2359_);
lean_closure_set(v___f_2360_, 3, v_____do__lift_2343_);
lean_closure_set(v___f_2360_, 4, v_x_2344_);
lean_closure_set(v___f_2360_, 5, v_toPure_2345_);
lean_closure_set(v___f_2360_, 6, v_inst_2346_);
lean_closure_set(v___f_2360_, 7, v___f_2347_);
lean_closure_set(v___f_2360_, 8, v_toBind_2348_);
lean_closure_set(v___f_2360_, 9, v_setNextMacroScope_2349_);
lean_closure_set(v___f_2360_, 10, v_inst_2350_);
lean_closure_set(v___f_2360_, 11, v_inst_2351_);
lean_closure_set(v___f_2360_, 12, v_inst_2352_);
lean_closure_set(v___f_2360_, 13, v_toMonadRef_2353_);
lean_closure_set(v___f_2360_, 14, v_inst_2354_);
lean_closure_set(v___f_2360_, 15, v_inst_2355_);
lean_closure_set(v___f_2360_, 16, v_toMonadExceptOf_2356_);
lean_closure_set(v___f_2360_, 17, v_getNextMacroScope_2357_);
v___x_2361_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v_getContext_2358_, v___f_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_inst_2362_ = _args[0];
lean_object* v_methods_2363_ = _args[1];
lean_object* v_____do__lift_2364_ = _args[2];
lean_object* v_x_2365_ = _args[3];
lean_object* v_toPure_2366_ = _args[4];
lean_object* v_inst_2367_ = _args[5];
lean_object* v___f_2368_ = _args[6];
lean_object* v_toBind_2369_ = _args[7];
lean_object* v_setNextMacroScope_2370_ = _args[8];
lean_object* v_inst_2371_ = _args[9];
lean_object* v_inst_2372_ = _args[10];
lean_object* v_inst_2373_ = _args[11];
lean_object* v_toMonadRef_2374_ = _args[12];
lean_object* v_inst_2375_ = _args[13];
lean_object* v_inst_2376_ = _args[14];
lean_object* v_toMonadExceptOf_2377_ = _args[15];
lean_object* v_getNextMacroScope_2378_ = _args[16];
lean_object* v_getContext_2379_ = _args[17];
lean_object* v_____do__lift_2380_ = _args[18];
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_inst_2362_, v_methods_2363_, v_____do__lift_2364_, v_x_2365_, v_toPure_2366_, v_inst_2367_, v___f_2368_, v_toBind_2369_, v_setNextMacroScope_2370_, v_inst_2371_, v_inst_2372_, v_inst_2373_, v_toMonadRef_2374_, v_inst_2375_, v_inst_2376_, v_toMonadExceptOf_2377_, v_getNextMacroScope_2378_, v_getContext_2379_, v_____do__lift_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_toMonadQuotation_2382_, lean_object* v_inst_2383_, lean_object* v_methods_2384_, lean_object* v_x_2385_, lean_object* v_toPure_2386_, lean_object* v_inst_2387_, lean_object* v___f_2388_, lean_object* v_toBind_2389_, lean_object* v_setNextMacroScope_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_toMonadRef_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_toMonadExceptOf_2397_, lean_object* v_getNextMacroScope_2398_, lean_object* v_____do__lift_2399_){
_start:
{
lean_object* v_getCurrMacroScope_2400_; lean_object* v_getContext_2401_; lean_object* v___f_2402_; lean_object* v___x_2403_; 
v_getCurrMacroScope_2400_ = lean_ctor_get(v_toMonadQuotation_2382_, 1);
lean_inc(v_getCurrMacroScope_2400_);
v_getContext_2401_ = lean_ctor_get(v_toMonadQuotation_2382_, 2);
lean_inc(v_getContext_2401_);
lean_dec_ref(v_toMonadQuotation_2382_);
lean_inc(v_toBind_2389_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 19, 18);
lean_closure_set(v___f_2402_, 0, v_inst_2383_);
lean_closure_set(v___f_2402_, 1, v_methods_2384_);
lean_closure_set(v___f_2402_, 2, v_____do__lift_2399_);
lean_closure_set(v___f_2402_, 3, v_x_2385_);
lean_closure_set(v___f_2402_, 4, v_toPure_2386_);
lean_closure_set(v___f_2402_, 5, v_inst_2387_);
lean_closure_set(v___f_2402_, 6, v___f_2388_);
lean_closure_set(v___f_2402_, 7, v_toBind_2389_);
lean_closure_set(v___f_2402_, 8, v_setNextMacroScope_2390_);
lean_closure_set(v___f_2402_, 9, v_inst_2391_);
lean_closure_set(v___f_2402_, 10, v_inst_2392_);
lean_closure_set(v___f_2402_, 11, v_inst_2393_);
lean_closure_set(v___f_2402_, 12, v_toMonadRef_2394_);
lean_closure_set(v___f_2402_, 13, v_inst_2395_);
lean_closure_set(v___f_2402_, 14, v_inst_2396_);
lean_closure_set(v___f_2402_, 15, v_toMonadExceptOf_2397_);
lean_closure_set(v___f_2402_, 16, v_getNextMacroScope_2398_);
lean_closure_set(v___f_2402_, 17, v_getContext_2401_);
v___x_2403_ = lean_apply_4(v_toBind_2389_, lean_box(0), lean_box(0), v_getCurrMacroScope_2400_, v___f_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2404_ = _args[0];
lean_object* v_inst_2405_ = _args[1];
lean_object* v_methods_2406_ = _args[2];
lean_object* v_x_2407_ = _args[3];
lean_object* v_toPure_2408_ = _args[4];
lean_object* v_inst_2409_ = _args[5];
lean_object* v___f_2410_ = _args[6];
lean_object* v_toBind_2411_ = _args[7];
lean_object* v_setNextMacroScope_2412_ = _args[8];
lean_object* v_inst_2413_ = _args[9];
lean_object* v_inst_2414_ = _args[10];
lean_object* v_inst_2415_ = _args[11];
lean_object* v_toMonadRef_2416_ = _args[12];
lean_object* v_inst_2417_ = _args[13];
lean_object* v_inst_2418_ = _args[14];
lean_object* v_toMonadExceptOf_2419_ = _args[15];
lean_object* v_getNextMacroScope_2420_ = _args[16];
lean_object* v_____do__lift_2421_ = _args[17];
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_toMonadQuotation_2404_, v_inst_2405_, v_methods_2406_, v_x_2407_, v_toPure_2408_, v_inst_2409_, v___f_2410_, v_toBind_2411_, v_setNextMacroScope_2412_, v_inst_2413_, v_inst_2414_, v_inst_2415_, v_toMonadRef_2416_, v_inst_2417_, v_inst_2418_, v_toMonadExceptOf_2419_, v_getNextMacroScope_2420_, v_____do__lift_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_toMonadRef_2423_, lean_object* v_env_2424_, lean_object* v_currNamespace_2425_, lean_object* v_opts_2426_, lean_object* v___x_2427_, lean_object* v___f_2428_, lean_object* v___f_2429_, lean_object* v_toMonadQuotation_2430_, lean_object* v_inst_2431_, lean_object* v_x_2432_, lean_object* v_toPure_2433_, lean_object* v_inst_2434_, lean_object* v___f_2435_, lean_object* v_toBind_2436_, lean_object* v_setNextMacroScope_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_toMonadExceptOf_2443_, lean_object* v_getNextMacroScope_2444_, lean_object* v_openDecls_2445_){
_start:
{
lean_object* v_getRef_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; lean_object* v_methods_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v_getRef_2446_ = lean_ctor_get(v_toMonadRef_2423_, 0);
lean_inc(v_getRef_2446_);
lean_inc(v_openDecls_2445_);
lean_inc(v_currNamespace_2425_);
lean_inc_ref(v_env_2424_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2447_, 0, v_env_2424_);
lean_closure_set(v___f_2447_, 1, v_currNamespace_2425_);
lean_closure_set(v___f_2447_, 2, v_openDecls_2445_);
lean_inc(v_currNamespace_2425_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 7, 4);
lean_closure_set(v___f_2448_, 0, v_env_2424_);
lean_closure_set(v___f_2448_, 1, v_opts_2426_);
lean_closure_set(v___f_2448_, 2, v_currNamespace_2425_);
lean_closure_set(v___f_2448_, 3, v_openDecls_2445_);
v___x_2449_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2449_, 0, lean_box(0));
lean_closure_set(v___x_2449_, 1, lean_box(0));
lean_closure_set(v___x_2449_, 2, v___x_2427_);
lean_closure_set(v___x_2449_, 3, lean_box(0));
lean_closure_set(v___x_2449_, 4, v_currNamespace_2425_);
v_methods_2450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2450_, 0, v___f_2428_);
lean_ctor_set(v_methods_2450_, 1, v___x_2449_);
lean_ctor_set(v_methods_2450_, 2, v___f_2429_);
lean_ctor_set(v_methods_2450_, 3, v___f_2447_);
lean_ctor_set(v_methods_2450_, 4, v___f_2448_);
lean_inc(v_toBind_2436_);
v___f_2451_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 18, 17);
lean_closure_set(v___f_2451_, 0, v_toMonadQuotation_2430_);
lean_closure_set(v___f_2451_, 1, v_inst_2431_);
lean_closure_set(v___f_2451_, 2, v_methods_2450_);
lean_closure_set(v___f_2451_, 3, v_x_2432_);
lean_closure_set(v___f_2451_, 4, v_toPure_2433_);
lean_closure_set(v___f_2451_, 5, v_inst_2434_);
lean_closure_set(v___f_2451_, 6, v___f_2435_);
lean_closure_set(v___f_2451_, 7, v_toBind_2436_);
lean_closure_set(v___f_2451_, 8, v_setNextMacroScope_2437_);
lean_closure_set(v___f_2451_, 9, v_inst_2438_);
lean_closure_set(v___f_2451_, 10, v_inst_2439_);
lean_closure_set(v___f_2451_, 11, v_inst_2440_);
lean_closure_set(v___f_2451_, 12, v_toMonadRef_2423_);
lean_closure_set(v___f_2451_, 13, v_inst_2441_);
lean_closure_set(v___f_2451_, 14, v_inst_2442_);
lean_closure_set(v___f_2451_, 15, v_toMonadExceptOf_2443_);
lean_closure_set(v___f_2451_, 16, v_getNextMacroScope_2444_);
v___x_2452_ = lean_apply_4(v_toBind_2436_, lean_box(0), lean_box(0), v_getRef_2446_, v___f_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_toMonadRef_2453_ = _args[0];
lean_object* v_env_2454_ = _args[1];
lean_object* v_currNamespace_2455_ = _args[2];
lean_object* v_opts_2456_ = _args[3];
lean_object* v___x_2457_ = _args[4];
lean_object* v___f_2458_ = _args[5];
lean_object* v___f_2459_ = _args[6];
lean_object* v_toMonadQuotation_2460_ = _args[7];
lean_object* v_inst_2461_ = _args[8];
lean_object* v_x_2462_ = _args[9];
lean_object* v_toPure_2463_ = _args[10];
lean_object* v_inst_2464_ = _args[11];
lean_object* v___f_2465_ = _args[12];
lean_object* v_toBind_2466_ = _args[13];
lean_object* v_setNextMacroScope_2467_ = _args[14];
lean_object* v_inst_2468_ = _args[15];
lean_object* v_inst_2469_ = _args[16];
lean_object* v_inst_2470_ = _args[17];
lean_object* v_inst_2471_ = _args[18];
lean_object* v_inst_2472_ = _args[19];
lean_object* v_toMonadExceptOf_2473_ = _args[20];
lean_object* v_getNextMacroScope_2474_ = _args[21];
lean_object* v_openDecls_2475_ = _args[22];
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_toMonadRef_2453_, v_env_2454_, v_currNamespace_2455_, v_opts_2456_, v___x_2457_, v___f_2458_, v___f_2459_, v_toMonadQuotation_2460_, v_inst_2461_, v_x_2462_, v_toPure_2463_, v_inst_2464_, v___f_2465_, v_toBind_2466_, v_setNextMacroScope_2467_, v_inst_2468_, v_inst_2469_, v_inst_2470_, v_inst_2471_, v_inst_2472_, v_toMonadExceptOf_2473_, v_getNextMacroScope_2474_, v_openDecls_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadRef_2477_, lean_object* v_env_2478_, lean_object* v_opts_2479_, lean_object* v___x_2480_, lean_object* v___f_2481_, lean_object* v___f_2482_, lean_object* v_toMonadQuotation_2483_, lean_object* v_inst_2484_, lean_object* v_x_2485_, lean_object* v_toPure_2486_, lean_object* v_inst_2487_, lean_object* v___f_2488_, lean_object* v_toBind_2489_, lean_object* v_setNextMacroScope_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_toMonadExceptOf_2496_, lean_object* v_getNextMacroScope_2497_, lean_object* v_getOpenDecls_2498_, lean_object* v_currNamespace_2499_){
_start:
{
lean_object* v___f_2500_; lean_object* v___x_2501_; 
lean_inc(v_toBind_2489_);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_2500_, 0, v_toMonadRef_2477_);
lean_closure_set(v___f_2500_, 1, v_env_2478_);
lean_closure_set(v___f_2500_, 2, v_currNamespace_2499_);
lean_closure_set(v___f_2500_, 3, v_opts_2479_);
lean_closure_set(v___f_2500_, 4, v___x_2480_);
lean_closure_set(v___f_2500_, 5, v___f_2481_);
lean_closure_set(v___f_2500_, 6, v___f_2482_);
lean_closure_set(v___f_2500_, 7, v_toMonadQuotation_2483_);
lean_closure_set(v___f_2500_, 8, v_inst_2484_);
lean_closure_set(v___f_2500_, 9, v_x_2485_);
lean_closure_set(v___f_2500_, 10, v_toPure_2486_);
lean_closure_set(v___f_2500_, 11, v_inst_2487_);
lean_closure_set(v___f_2500_, 12, v___f_2488_);
lean_closure_set(v___f_2500_, 13, v_toBind_2489_);
lean_closure_set(v___f_2500_, 14, v_setNextMacroScope_2490_);
lean_closure_set(v___f_2500_, 15, v_inst_2491_);
lean_closure_set(v___f_2500_, 16, v_inst_2492_);
lean_closure_set(v___f_2500_, 17, v_inst_2493_);
lean_closure_set(v___f_2500_, 18, v_inst_2494_);
lean_closure_set(v___f_2500_, 19, v_inst_2495_);
lean_closure_set(v___f_2500_, 20, v_toMonadExceptOf_2496_);
lean_closure_set(v___f_2500_, 21, v_getNextMacroScope_2497_);
v___x_2501_ = lean_apply_4(v_toBind_2489_, lean_box(0), lean_box(0), v_getOpenDecls_2498_, v___f_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadRef_2502_ = _args[0];
lean_object* v_env_2503_ = _args[1];
lean_object* v_opts_2504_ = _args[2];
lean_object* v___x_2505_ = _args[3];
lean_object* v___f_2506_ = _args[4];
lean_object* v___f_2507_ = _args[5];
lean_object* v_toMonadQuotation_2508_ = _args[6];
lean_object* v_inst_2509_ = _args[7];
lean_object* v_x_2510_ = _args[8];
lean_object* v_toPure_2511_ = _args[9];
lean_object* v_inst_2512_ = _args[10];
lean_object* v___f_2513_ = _args[11];
lean_object* v_toBind_2514_ = _args[12];
lean_object* v_setNextMacroScope_2515_ = _args[13];
lean_object* v_inst_2516_ = _args[14];
lean_object* v_inst_2517_ = _args[15];
lean_object* v_inst_2518_ = _args[16];
lean_object* v_inst_2519_ = _args[17];
lean_object* v_inst_2520_ = _args[18];
lean_object* v_toMonadExceptOf_2521_ = _args[19];
lean_object* v_getNextMacroScope_2522_ = _args[20];
lean_object* v_getOpenDecls_2523_ = _args[21];
lean_object* v_currNamespace_2524_ = _args[22];
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadRef_2502_, v_env_2503_, v_opts_2504_, v___x_2505_, v___f_2506_, v___f_2507_, v_toMonadQuotation_2508_, v_inst_2509_, v_x_2510_, v_toPure_2511_, v_inst_2512_, v___f_2513_, v_toBind_2514_, v_setNextMacroScope_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_inst_2519_, v_inst_2520_, v_toMonadExceptOf_2521_, v_getNextMacroScope_2522_, v_getOpenDecls_2523_, v_currNamespace_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_inst_2526_, lean_object* v_toMonadRef_2527_, lean_object* v_env_2528_, lean_object* v___x_2529_, lean_object* v___f_2530_, lean_object* v___f_2531_, lean_object* v_toMonadQuotation_2532_, lean_object* v_inst_2533_, lean_object* v_x_2534_, lean_object* v_toPure_2535_, lean_object* v_inst_2536_, lean_object* v___f_2537_, lean_object* v_toBind_2538_, lean_object* v_setNextMacroScope_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_toMonadExceptOf_2545_, lean_object* v_getNextMacroScope_2546_, lean_object* v_opts_2547_){
_start:
{
lean_object* v_getCurrNamespace_2548_; lean_object* v_getOpenDecls_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; 
v_getCurrNamespace_2548_ = lean_ctor_get(v_inst_2526_, 0);
lean_inc(v_getCurrNamespace_2548_);
v_getOpenDecls_2549_ = lean_ctor_get(v_inst_2526_, 1);
lean_inc(v_getOpenDecls_2549_);
lean_dec_ref(v_inst_2526_);
lean_inc(v_toBind_2538_);
v___f_2550_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 23, 22);
lean_closure_set(v___f_2550_, 0, v_toMonadRef_2527_);
lean_closure_set(v___f_2550_, 1, v_env_2528_);
lean_closure_set(v___f_2550_, 2, v_opts_2547_);
lean_closure_set(v___f_2550_, 3, v___x_2529_);
lean_closure_set(v___f_2550_, 4, v___f_2530_);
lean_closure_set(v___f_2550_, 5, v___f_2531_);
lean_closure_set(v___f_2550_, 6, v_toMonadQuotation_2532_);
lean_closure_set(v___f_2550_, 7, v_inst_2533_);
lean_closure_set(v___f_2550_, 8, v_x_2534_);
lean_closure_set(v___f_2550_, 9, v_toPure_2535_);
lean_closure_set(v___f_2550_, 10, v_inst_2536_);
lean_closure_set(v___f_2550_, 11, v___f_2537_);
lean_closure_set(v___f_2550_, 12, v_toBind_2538_);
lean_closure_set(v___f_2550_, 13, v_setNextMacroScope_2539_);
lean_closure_set(v___f_2550_, 14, v_inst_2540_);
lean_closure_set(v___f_2550_, 15, v_inst_2541_);
lean_closure_set(v___f_2550_, 16, v_inst_2542_);
lean_closure_set(v___f_2550_, 17, v_inst_2543_);
lean_closure_set(v___f_2550_, 18, v_inst_2544_);
lean_closure_set(v___f_2550_, 19, v_toMonadExceptOf_2545_);
lean_closure_set(v___f_2550_, 20, v_getNextMacroScope_2546_);
lean_closure_set(v___f_2550_, 21, v_getOpenDecls_2549_);
v___x_2551_ = lean_apply_4(v_toBind_2538_, lean_box(0), lean_box(0), v_getCurrNamespace_2548_, v___f_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_inst_2552_ = _args[0];
lean_object* v_toMonadRef_2553_ = _args[1];
lean_object* v_env_2554_ = _args[2];
lean_object* v___x_2555_ = _args[3];
lean_object* v___f_2556_ = _args[4];
lean_object* v___f_2557_ = _args[5];
lean_object* v_toMonadQuotation_2558_ = _args[6];
lean_object* v_inst_2559_ = _args[7];
lean_object* v_x_2560_ = _args[8];
lean_object* v_toPure_2561_ = _args[9];
lean_object* v_inst_2562_ = _args[10];
lean_object* v___f_2563_ = _args[11];
lean_object* v_toBind_2564_ = _args[12];
lean_object* v_setNextMacroScope_2565_ = _args[13];
lean_object* v_inst_2566_ = _args[14];
lean_object* v_inst_2567_ = _args[15];
lean_object* v_inst_2568_ = _args[16];
lean_object* v_inst_2569_ = _args[17];
lean_object* v_inst_2570_ = _args[18];
lean_object* v_toMonadExceptOf_2571_ = _args[19];
lean_object* v_getNextMacroScope_2572_ = _args[20];
lean_object* v_opts_2573_ = _args[21];
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_inst_2552_, v_toMonadRef_2553_, v_env_2554_, v___x_2555_, v___f_2556_, v___f_2557_, v_toMonadQuotation_2558_, v_inst_2559_, v_x_2560_, v_toPure_2561_, v_inst_2562_, v___f_2563_, v_toBind_2564_, v_setNextMacroScope_2565_, v_inst_2566_, v_inst_2567_, v_inst_2568_, v_inst_2569_, v_inst_2570_, v_toMonadExceptOf_2571_, v_getNextMacroScope_2572_, v_opts_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_inst_2577_, lean_object* v_toMonadRef_2578_, lean_object* v___x_2579_, lean_object* v_toMonadQuotation_2580_, lean_object* v_inst_2581_, lean_object* v_x_2582_, lean_object* v_toPure_2583_, lean_object* v_inst_2584_, lean_object* v___f_2585_, lean_object* v_toBind_2586_, lean_object* v_setNextMacroScope_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_toMonadExceptOf_2593_, lean_object* v_getNextMacroScope_2594_, lean_object* v_env_2595_){
_start:
{
lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; 
lean_inc_ref(v_env_2595_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2596_, 0, v_env_2595_);
lean_closure_set(v___f_2596_, 1, v___x_2575_);
lean_closure_set(v___f_2596_, 2, v___x_2576_);
lean_inc_ref(v_env_2595_);
v___f_2597_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2597_, 0, v_env_2595_);
lean_inc(v_inst_2590_);
lean_inc(v_toBind_2586_);
v___f_2598_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 22, 21);
lean_closure_set(v___f_2598_, 0, v_inst_2577_);
lean_closure_set(v___f_2598_, 1, v_toMonadRef_2578_);
lean_closure_set(v___f_2598_, 2, v_env_2595_);
lean_closure_set(v___f_2598_, 3, v___x_2579_);
lean_closure_set(v___f_2598_, 4, v___f_2596_);
lean_closure_set(v___f_2598_, 5, v___f_2597_);
lean_closure_set(v___f_2598_, 6, v_toMonadQuotation_2580_);
lean_closure_set(v___f_2598_, 7, v_inst_2581_);
lean_closure_set(v___f_2598_, 8, v_x_2582_);
lean_closure_set(v___f_2598_, 9, v_toPure_2583_);
lean_closure_set(v___f_2598_, 10, v_inst_2584_);
lean_closure_set(v___f_2598_, 11, v___f_2585_);
lean_closure_set(v___f_2598_, 12, v_toBind_2586_);
lean_closure_set(v___f_2598_, 13, v_setNextMacroScope_2587_);
lean_closure_set(v___f_2598_, 14, v_inst_2588_);
lean_closure_set(v___f_2598_, 15, v_inst_2589_);
lean_closure_set(v___f_2598_, 16, v_inst_2590_);
lean_closure_set(v___f_2598_, 17, v_inst_2591_);
lean_closure_set(v___f_2598_, 18, v_inst_2592_);
lean_closure_set(v___f_2598_, 19, v_toMonadExceptOf_2593_);
lean_closure_set(v___f_2598_, 20, v_getNextMacroScope_2594_);
v___x_2599_ = lean_apply_4(v_toBind_2586_, lean_box(0), lean_box(0), v_inst_2590_, v___f_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v___x_2600_ = _args[0];
lean_object* v___x_2601_ = _args[1];
lean_object* v_inst_2602_ = _args[2];
lean_object* v_toMonadRef_2603_ = _args[3];
lean_object* v___x_2604_ = _args[4];
lean_object* v_toMonadQuotation_2605_ = _args[5];
lean_object* v_inst_2606_ = _args[6];
lean_object* v_x_2607_ = _args[7];
lean_object* v_toPure_2608_ = _args[8];
lean_object* v_inst_2609_ = _args[9];
lean_object* v___f_2610_ = _args[10];
lean_object* v_toBind_2611_ = _args[11];
lean_object* v_setNextMacroScope_2612_ = _args[12];
lean_object* v_inst_2613_ = _args[13];
lean_object* v_inst_2614_ = _args[14];
lean_object* v_inst_2615_ = _args[15];
lean_object* v_inst_2616_ = _args[16];
lean_object* v_inst_2617_ = _args[17];
lean_object* v_toMonadExceptOf_2618_ = _args[18];
lean_object* v_getNextMacroScope_2619_ = _args[19];
lean_object* v_env_2620_ = _args[20];
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v___x_2600_, v___x_2601_, v_inst_2602_, v_toMonadRef_2603_, v___x_2604_, v_toMonadQuotation_2605_, v_inst_2606_, v_x_2607_, v_toPure_2608_, v_inst_2609_, v___f_2610_, v_toBind_2611_, v_setNextMacroScope_2612_, v_inst_2613_, v_inst_2614_, v_inst_2615_, v_inst_2616_, v_inst_2617_, v_toMonadExceptOf_2618_, v_getNextMacroScope_2619_, v_env_2620_);
return v_res_2621_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_EStateM_nonBacktrackable(lean_box(0));
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2643_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___f_2645_; 
v___x_2644_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2645_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2645_, 0, v___x_2644_);
return v___f_2645_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___f_2647_; 
v___x_2646_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2647_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2647_, 0, v___x_2646_);
return v___f_2647_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v___f_2648_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2649_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___f_2649_);
lean_ctor_set(v___x_2650_, 1, v___f_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v_toApplicative_2665_; lean_object* v_toBind_2666_; lean_object* v_getEnv_2667_; lean_object* v_toMonadExceptOf_2668_; lean_object* v_toMonadRef_2669_; lean_object* v_toMonadQuotation_2670_; lean_object* v_getNextMacroScope_2671_; lean_object* v_setNextMacroScope_2672_; lean_object* v_toPure_2673_; lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v___x_2663_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2664_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2665_ = lean_ctor_get(v_inst_2653_, 0);
v_toBind_2666_ = lean_ctor_get(v_inst_2653_, 1);
lean_inc(v_toBind_2666_);
v_getEnv_2667_ = lean_ctor_get(v_inst_2655_, 0);
lean_inc(v_getEnv_2667_);
v_toMonadExceptOf_2668_ = lean_ctor_get(v_inst_2657_, 0);
lean_inc_ref(v_toMonadExceptOf_2668_);
v_toMonadRef_2669_ = lean_ctor_get(v_inst_2657_, 1);
lean_inc_ref(v_toMonadRef_2669_);
v_toMonadQuotation_2670_ = lean_ctor_get(v_inst_2654_, 0);
lean_inc_ref(v_toMonadQuotation_2670_);
v_getNextMacroScope_2671_ = lean_ctor_get(v_inst_2654_, 1);
lean_inc(v_getNextMacroScope_2671_);
v_setNextMacroScope_2672_ = lean_ctor_get(v_inst_2654_, 2);
lean_inc(v_setNextMacroScope_2672_);
lean_dec_ref(v_inst_2654_);
v_toPure_2673_ = lean_ctor_get(v_toApplicative_2665_, 1);
lean_inc(v_toPure_2673_);
v___x_2674_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_toBind_2666_);
lean_inc(v_inst_2660_);
lean_inc(v_inst_2661_);
lean_inc_ref(v_toMonadRef_2669_);
lean_inc_ref(v_inst_2659_);
lean_inc_ref(v_inst_2653_);
lean_inc(v_toPure_2673_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 8, 7);
lean_closure_set(v___f_2675_, 0, v_toPure_2673_);
lean_closure_set(v___f_2675_, 1, v_inst_2653_);
lean_closure_set(v___f_2675_, 2, v_inst_2659_);
lean_closure_set(v___f_2675_, 3, v_toMonadRef_2669_);
lean_closure_set(v___f_2675_, 4, v_inst_2661_);
lean_closure_set(v___f_2675_, 5, v_inst_2660_);
lean_closure_set(v___f_2675_, 6, v_toBind_2666_);
lean_inc(v_toBind_2666_);
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 21, 20);
lean_closure_set(v___f_2676_, 0, v___x_2664_);
lean_closure_set(v___f_2676_, 1, v___x_2674_);
lean_closure_set(v___f_2676_, 2, v_inst_2658_);
lean_closure_set(v___f_2676_, 3, v_toMonadRef_2669_);
lean_closure_set(v___f_2676_, 4, v___x_2663_);
lean_closure_set(v___f_2676_, 5, v_toMonadQuotation_2670_);
lean_closure_set(v___f_2676_, 6, v_inst_2656_);
lean_closure_set(v___f_2676_, 7, v_x_2662_);
lean_closure_set(v___f_2676_, 8, v_toPure_2673_);
lean_closure_set(v___f_2676_, 9, v_inst_2653_);
lean_closure_set(v___f_2676_, 10, v___f_2675_);
lean_closure_set(v___f_2676_, 11, v_toBind_2666_);
lean_closure_set(v___f_2676_, 12, v_setNextMacroScope_2672_);
lean_closure_set(v___f_2676_, 13, v_inst_2655_);
lean_closure_set(v___f_2676_, 14, v_inst_2659_);
lean_closure_set(v___f_2676_, 15, v_inst_2660_);
lean_closure_set(v___f_2676_, 16, v_inst_2661_);
lean_closure_set(v___f_2676_, 17, v_inst_2657_);
lean_closure_set(v___f_2676_, 18, v_toMonadExceptOf_2668_);
lean_closure_set(v___f_2676_, 19, v_getNextMacroScope_2671_);
v___x_2677_ = lean_apply_4(v_toBind_2666_, lean_box(0), lean_box(0), v_getEnv_2667_, v___f_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2678_, lean_object* v_00_u03b1_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_inst_2684_, v_inst_2685_, v_inst_2686_, v_inst_2687_, v_inst_2688_, v_x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2692_, lean_object* v_00_u03b1_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_x_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Elab_liftMacroM(v_m_2692_, v_00_u03b1_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_x_2704_);
lean_dec(v_inst_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_x_2715_, lean_object* v_stx_2716_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_apply_1(v_x_2715_, v_stx_2716_);
v___x_2718_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_inst_2712_, v_inst_2713_, v_inst_2714_, v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_x_2730_, lean_object* v_stx_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_apply_1(v_x_2730_, v_stx_2731_);
v___x_2733_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_inst_2725_, v_inst_2726_, v_inst_2727_, v_inst_2728_, v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_x_2745_, lean_object* v_stx_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Elab_adaptMacro(v_m_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_inst_2744_, v_x_2745_, v_stx_2746_);
lean_dec(v_inst_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2748_, lean_object* v_currNamespace_2749_, lean_object* v_idx_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_name_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_inc(v_idx_2750_);
lean_inc(v_baseName_2748_);
v_name_2753_ = lean_name_append_index_after(v_baseName_2748_, v_idx_2750_);
lean_inc(v_name_2753_);
lean_inc(v_currNamespace_2749_);
v___x_2754_ = l_Lean_Name_append(v_currNamespace_2749_, v_name_2753_);
v___x_2755_ = l_Lean_Macro_hasDecl(v___x_2754_, v_a_2751_, v_a_2752_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; uint8_t v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
v___x_2757_ = lean_unbox(v_a_2756_);
lean_dec(v_a_2756_);
if (v___x_2757_ == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_idx_2750_);
lean_dec(v_currNamespace_2749_);
lean_dec(v_baseName_2748_);
v_a_2758_ = lean_ctor_get(v___x_2755_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v___x_2755_, 0);
lean_dec(v_unused_2766_);
v___x_2760_ = v___x_2755_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2755_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_name_2753_);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_name_2753_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec(v_name_2753_);
v_a_2767_ = lean_ctor_get(v___x_2755_, 1);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2755_);
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = lean_nat_add(v_idx_2750_, v___x_2768_);
lean_dec(v_idx_2750_);
v_idx_2750_ = v___x_2769_;
v_a_2752_ = v_a_2767_;
goto _start;
}
}
else
{
lean_object* v_a_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_name_2753_);
lean_dec(v_idx_2750_);
lean_dec(v_currNamespace_2749_);
lean_dec(v_baseName_2748_);
v_a_2771_ = lean_ctor_get(v___x_2755_, 0);
v_a_2772_ = lean_ctor_get(v___x_2755_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2755_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_inc(v_a_2771_);
lean_dec(v___x_2755_);
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
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_a_2772_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2780_, lean_object* v_currNamespace_2781_, lean_object* v_idx_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2780_, v_currNamespace_2781_, v_idx_2782_, v_a_2783_, v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Macro_getCurrNamespace(v_a_2787_, v_a_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
v_a_2791_ = lean_ctor_get(v___x_2789_, 1);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2789_);
lean_inc(v_baseName_2786_);
lean_inc(v_a_2790_);
v___x_2792_ = l_Lean_Name_append(v_a_2790_, v_baseName_2786_);
v___x_2793_ = l_Lean_Macro_hasDecl(v___x_2792_, v_a_2787_, v_a_2791_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; uint8_t v___x_2795_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
v___x_2795_ = lean_unbox(v_a_2794_);
lean_dec(v_a_2794_);
if (v___x_2795_ == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2790_);
v_a_2796_ = lean_ctor_get(v___x_2793_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2793_, 0);
lean_dec(v_unused_2804_);
v___x_2798_ = v___x_2793_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2793_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v_baseName_2786_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_baseName_2786_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2793_, 1);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2793_);
v___x_2806_ = lean_unsigned_to_nat(1u);
v___x_2807_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2786_, v_a_2790_, v___x_2806_, v_a_2787_, v_a_2805_);
return v___x_2807_;
}
}
else
{
lean_object* v_a_2808_; lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2790_);
lean_dec(v_baseName_2786_);
v_a_2808_ = lean_ctor_get(v___x_2793_, 0);
v_a_2809_ = lean_ctor_get(v___x_2793_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2793_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_inc(v_a_2808_);
lean_dec(v___x_2793_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2808_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_dec(v_baseName_2786_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2817_, v_a_2818_, v_a_2819_);
lean_dec_ref(v_a_2818_);
return v_res_2820_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_name_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2829_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2830_ = l_Lean_MessageData_ofName(v_name_2828_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_logError___redArg(v_inst_2824_, v_inst_2825_, v_inst_2826_, v_inst_2827_, v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_ex_2838_){
_start:
{
if (lean_obj_tag(v_ex_2838_) == 0)
{
lean_object* v_ref_2839_; lean_object* v_msg_2840_; lean_object* v___x_2841_; 
lean_dec(v_inst_2837_);
v_ref_2839_ = lean_ctor_get(v_ex_2838_, 0);
lean_inc(v_ref_2839_);
v_msg_2840_ = lean_ctor_get(v_ex_2838_, 1);
lean_inc_ref(v_msg_2840_);
lean_dec_ref(v_ex_2838_);
v___x_2841_ = l_Lean_logErrorAt___redArg(v_inst_2833_, v_inst_2834_, v_inst_2835_, v_inst_2836_, v_ref_2839_, v_msg_2840_);
return v___x_2841_;
}
else
{
lean_object* v_id_2842_; lean_object* v___f_2843_; uint8_t v___y_2845_; uint8_t v___x_2854_; 
v_id_2842_ = lean_ctor_get(v_ex_2838_, 0);
lean_inc(v_id_2842_);
lean_inc_ref(v_inst_2833_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2843_, 0, v_inst_2833_);
lean_closure_set(v___f_2843_, 1, v_inst_2834_);
lean_closure_set(v___f_2843_, 2, v_inst_2835_);
lean_closure_set(v___f_2843_, 3, v_inst_2836_);
v___x_2854_ = l_Lean_Elab_isAbortExceptionId(v_id_2842_);
if (v___x_2854_ == 0)
{
uint8_t v___x_2855_; 
v___x_2855_ = l_Lean_Exception_isInterrupt(v_ex_2838_);
lean_dec_ref(v_ex_2838_);
v___y_2845_ = v___x_2855_;
goto v___jp_2844_;
}
else
{
lean_dec_ref(v_ex_2838_);
v___y_2845_ = v___x_2854_;
goto v___jp_2844_;
}
v___jp_2844_:
{
if (v___y_2845_ == 0)
{
lean_object* v_toBind_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_toBind_2846_ = lean_ctor_get(v_inst_2833_, 1);
lean_inc(v_toBind_2846_);
lean_dec_ref(v_inst_2833_);
v___x_2847_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2847_, 0, v_id_2842_);
v___x_2848_ = lean_apply_2(v_inst_2837_, lean_box(0), v___x_2847_);
v___x_2849_ = lean_apply_4(v_toBind_2846_, lean_box(0), lean_box(0), v___x_2848_, v___f_2843_);
return v___x_2849_;
}
else
{
lean_object* v_toApplicative_2850_; lean_object* v_toPure_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v___f_2843_);
lean_dec(v_id_2842_);
lean_dec(v_inst_2837_);
v_toApplicative_2850_ = lean_ctor_get(v_inst_2833_, 0);
lean_inc_ref(v_toApplicative_2850_);
lean_dec_ref(v_inst_2833_);
v_toPure_2851_ = lean_ctor_get(v_toApplicative_2850_, 1);
lean_inc(v_toPure_2851_);
lean_dec_ref(v_toApplicative_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_apply_2(v_toPure_2851_, lean_box(0), v___x_2852_);
return v___x_2853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_ex_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_Elab_logException___redArg(v_inst_2857_, v_inst_2858_, v_inst_2859_, v_inst_2860_, v_inst_2861_, v_ex_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_ex_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Elab_logException___redArg(v_inst_2864_, v_inst_2865_, v_inst_2866_, v_inst_2867_, v_inst_2868_, v_ex_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v_tryCatch_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v_tryCatch_2878_ = lean_ctor_get(v_inst_2873_, 1);
lean_inc(v_tryCatch_2878_);
lean_dec_ref(v_inst_2873_);
v___f_2879_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2879_, 0, v_inst_2871_);
lean_closure_set(v___f_2879_, 1, v_inst_2872_);
lean_closure_set(v___f_2879_, 2, v_inst_2874_);
lean_closure_set(v___f_2879_, 3, v_inst_2875_);
lean_closure_set(v___f_2879_, 4, v_inst_2876_);
v___x_2880_ = lean_apply_3(v_tryCatch_2878_, lean_box(0), v_x_2877_, v___f_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_x_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_withLogging___redArg(v_inst_2882_, v_inst_2883_, v_inst_2884_, v_inst_2885_, v_inst_2886_, v_inst_2887_, v_x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2892_ = l_Lean_stringToMessageData(v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2893_, lean_object* v_ex_2894_, lean_object* v_toPure_2895_, lean_object* v_____do__lift_2896_){
_start:
{
lean_object* v_exPosition_2897_; lean_object* v_line_2898_; lean_object* v_column_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2919_; 
v_exPosition_2897_ = l_Lean_FileMap_toPosition(v_____do__lift_2896_, v_val_2893_);
v_line_2898_ = lean_ctor_get(v_exPosition_2897_, 0);
v_column_2899_ = lean_ctor_get(v_exPosition_2897_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_exPosition_2897_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2901_ = v_exPosition_2897_;
v_isShared_2902_ = v_isSharedCheck_2919_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_column_2899_);
lean_inc(v_line_2898_);
lean_dec(v_exPosition_2897_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2919_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2903_ = l_Nat_reprFast(v_line_2898_);
v___x_2904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = l_Lean_MessageData_ofFormat(v___x_2904_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 7);
lean_ctor_set(v___x_2901_, 1, v___x_2906_);
lean_ctor_set(v___x_2901_, 0, v___x_2905_);
v___x_2908_ = v___x_2901_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2909_ = l_Nat_reprFast(v_column_2899_);
v___x_2910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
v___x_2911_ = l_Lean_MessageData_ofFormat(v___x_2910_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2908_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_Exception_toMessageData(v_ex_2894_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_apply_2(v_toPure_2895_, lean_box(0), v___x_2916_);
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2920_, lean_object* v_ex_2921_, lean_object* v_toPure_2922_, lean_object* v_____do__lift_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2920_, v_ex_2921_, v_toPure_2922_, v_____do__lift_2923_);
lean_dec(v_val_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2925_, lean_object* v_toPure_2926_, lean_object* v_inst_2927_, lean_object* v_toBind_2928_, lean_object* v_pos_2929_){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = l_Lean_Exception_getRef(v_ex_2925_);
v___x_2931_ = 0;
v___x_2932_ = l_Lean_Syntax_getPos_x3f(v___x_2930_, v___x_2931_);
lean_dec(v___x_2930_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_toBind_2928_);
lean_dec_ref(v_inst_2927_);
v___x_2933_ = l_Lean_Exception_toMessageData(v_ex_2925_);
v___x_2934_ = lean_apply_2(v_toPure_2926_, lean_box(0), v___x_2933_);
return v___x_2934_;
}
else
{
lean_object* v_val_2935_; uint8_t v___x_2936_; 
v_val_2935_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_val_2935_);
lean_dec_ref(v___x_2932_);
v___x_2936_ = lean_nat_dec_eq(v_pos_2929_, v_val_2935_);
if (v___x_2936_ == 0)
{
lean_object* v_toMonadFileMap_2937_; lean_object* v___f_2938_; lean_object* v___x_2939_; 
v_toMonadFileMap_2937_ = lean_ctor_get(v_inst_2927_, 0);
lean_inc(v_toMonadFileMap_2937_);
lean_dec_ref(v_inst_2927_);
v___f_2938_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2938_, 0, v_val_2935_);
lean_closure_set(v___f_2938_, 1, v_ex_2925_);
lean_closure_set(v___f_2938_, 2, v_toPure_2926_);
v___x_2939_ = lean_apply_4(v_toBind_2928_, lean_box(0), lean_box(0), v_toMonadFileMap_2937_, v___f_2938_);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v_val_2935_);
lean_dec(v_toBind_2928_);
lean_dec_ref(v_inst_2927_);
v___x_2940_ = l_Lean_Exception_toMessageData(v_ex_2925_);
v___x_2941_ = lean_apply_2(v_toPure_2926_, lean_box(0), v___x_2940_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2942_, lean_object* v_toPure_2943_, lean_object* v_inst_2944_, lean_object* v_toBind_2945_, lean_object* v_pos_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2942_, v_toPure_2943_, v_inst_2944_, v_toBind_2945_, v_pos_2946_);
lean_dec(v_pos_2946_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_ex_2950_){
_start:
{
lean_object* v_toApplicative_2951_; lean_object* v_toBind_2952_; lean_object* v_toPure_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; lean_object* v___x_2956_; 
v_toApplicative_2951_ = lean_ctor_get(v_inst_2948_, 0);
v_toBind_2952_ = lean_ctor_get(v_inst_2948_, 1);
lean_inc(v_toBind_2952_);
v_toPure_2953_ = lean_ctor_get(v_toApplicative_2951_, 1);
lean_inc(v_toPure_2953_);
lean_inc_ref(v_inst_2949_);
v___x_2954_ = l_Lean_getRefPos___redArg(v_inst_2948_, v_inst_2949_);
lean_inc(v_toBind_2952_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2955_, 0, v_ex_2950_);
lean_closure_set(v___f_2955_, 1, v_toPure_2953_);
lean_closure_set(v___f_2955_, 2, v_inst_2949_);
lean_closure_set(v___f_2955_, 3, v_toBind_2952_);
v___x_2956_ = lean_apply_4(v_toBind_2952_, lean_box(0), lean_box(0), v___x_2954_, v___f_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_ex_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2958_, v_inst_2959_, v_ex_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2962_, v_inst_2963_, v_x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_____do__lift_2972_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2973_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_msg_2969_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_toMessageList(v_____do__lift_2972_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_throwError___redArg(v_inst_2970_, v_inst_2971_, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_msg_2981_, lean_object* v_exs_2982_){
_start:
{
lean_object* v_toBind_2983_; lean_object* v___f_2984_; lean_object* v___f_2985_; size_t v_sz_2986_; size_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_toBind_2983_ = lean_ctor_get(v_inst_2979_, 1);
lean_inc(v_toBind_2983_);
lean_inc_ref(v_inst_2979_);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2984_, 0, v_inst_2979_);
lean_closure_set(v___f_2984_, 1, v_inst_2980_);
lean_inc_ref(v_inst_2979_);
v___f_2985_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2985_, 0, v_msg_2981_);
lean_closure_set(v___f_2985_, 1, v_inst_2979_);
lean_closure_set(v___f_2985_, 2, v_inst_2978_);
v_sz_2986_ = lean_array_size(v_exs_2982_);
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2979_, v___f_2984_, v_sz_2986_, v___x_2987_, v_exs_2982_);
v___x_2989_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v___x_2988_, v___f_2985_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2990_, lean_object* v_00_u03b1_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_msg_2995_, lean_object* v_exs_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2992_, v_inst_2993_, v_inst_2994_, v_msg_2995_, v_exs_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3065_ = 0;
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3067_ = l_Lean_registerTraceClass(v___x_3064_, v___x_3065_, v___x_3066_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec_ref(v___x_3067_);
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3069_ = l_Lean_registerTraceClass(v___x_3068_, v___x_3065_, v___x_3066_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref(v___x_3069_);
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3071_ = 1;
v___x_3072_ = l_Lean_registerTraceClass(v___x_3070_, v___x_3071_, v___x_3066_);
return v___x_3072_;
}
else
{
return v___x_3069_;
}
}
else
{
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3074_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_pp_macroStack = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_pp_macroStack);
lean_dec_ref(res);
res = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_macroAttribute);
lean_dec_ref(res);
res = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
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
