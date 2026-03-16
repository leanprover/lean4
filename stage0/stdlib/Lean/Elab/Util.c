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
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_String_toFormat(lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_72_);
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
lean_dec_ref(v_a_72_);
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
lean_inc_ref(v_a_541_);
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
lean_dec_ref(v_a_541_);
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
lean_dec_ref(v_a_541_);
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
lean_dec_ref(v_a_541_);
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
lean_dec_ref(v_a_541_);
return v___x_554_;
}
else
{
lean_dec(v_a_545_);
lean_dec_ref(v_a_541_);
return v___y_547_;
}
}
}
else
{
lean_dec_ref(v_a_541_);
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
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
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
lean_object* v_fileName_863_; lean_object* v_fileMap_864_; lean_object* v_options_865_; lean_object* v_currRecDepth_866_; lean_object* v_maxRecDepth_867_; lean_object* v_ref_868_; lean_object* v_currNamespace_869_; lean_object* v_openDecls_870_; lean_object* v_initHeartbeats_871_; lean_object* v_maxHeartbeats_872_; lean_object* v_quotContext_873_; lean_object* v_currMacroScope_874_; uint8_t v_diag_875_; lean_object* v_cancelTk_x3f_876_; uint8_t v_suppressElabErrors_877_; lean_object* v_inheritedTraceOptions_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_887_; 
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
v_isSharedCheck_887_ = !lean_is_exclusive(v___y_860_);
if (v_isSharedCheck_887_ == 0)
{
v___x_880_ = v___y_860_;
v_isShared_881_ = v_isSharedCheck_887_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_inheritedTraceOptions_878_);
lean_inc(v_cancelTk_x3f_876_);
lean_inc(v_currMacroScope_874_);
lean_inc(v_quotContext_873_);
lean_inc(v_maxHeartbeats_872_);
lean_inc(v_initHeartbeats_871_);
lean_inc(v_openDecls_870_);
lean_inc(v_currNamespace_869_);
lean_inc(v_ref_868_);
lean_inc(v_maxRecDepth_867_);
lean_inc(v_currRecDepth_866_);
lean_inc(v_options_865_);
lean_inc(v_fileMap_864_);
lean_inc(v_fileName_863_);
lean_dec(v___y_860_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_887_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_ref_882_; lean_object* v___x_884_; 
v_ref_882_ = l_Lean_replaceRef(v_ref_858_, v_ref_868_);
lean_dec(v_ref_868_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 5, v_ref_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_fileName_863_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_fileMap_864_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_options_865_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_currRecDepth_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_maxRecDepth_867_);
lean_ctor_set(v_reuseFailAlloc_886_, 5, v_ref_882_);
lean_ctor_set(v_reuseFailAlloc_886_, 6, v_currNamespace_869_);
lean_ctor_set(v_reuseFailAlloc_886_, 7, v_openDecls_870_);
lean_ctor_set(v_reuseFailAlloc_886_, 8, v_initHeartbeats_871_);
lean_ctor_set(v_reuseFailAlloc_886_, 9, v_maxHeartbeats_872_);
lean_ctor_set(v_reuseFailAlloc_886_, 10, v_quotContext_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 11, v_currMacroScope_874_);
lean_ctor_set(v_reuseFailAlloc_886_, 12, v_cancelTk_x3f_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 13, v_inheritedTraceOptions_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*14, v_diag_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*14 + 1, v_suppressElabErrors_877_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_859_, v___x_884_, v___y_861_);
lean_dec_ref(v___x_884_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_888_, v_msg_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec(v_ref_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(lean_object* v_ref_894_, lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; lean_object* v_a_901_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18(v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_);
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_894_, v_a_901_, v___y_897_, v___y_898_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg___boxed(lean_object* v_ref_903_, lean_object* v_msg_904_, lean_object* v_declHint_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_903_, v_msg_904_, v_declHint_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec(v_ref_903_);
return v_res_909_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__0));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(lean_object* v_ref_913_, lean_object* v_constName_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_918_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___closed__1);
v___x_919_ = 0;
lean_inc(v_constName_914_);
v___x_920_ = l_Lean_MessageData_ofConstName(v_constName_914_, v___x_919_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_918_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_913_, v___x_923_, v_constName_914_, v___y_915_, v___y_916_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg___boxed(lean_object* v_ref_925_, lean_object* v_constName_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_925_, v_constName_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec(v_ref_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_ref_935_; lean_object* v___x_936_; 
v_ref_935_ = lean_ctor_get(v___y_932_, 5);
lean_inc(v_ref_935_);
v___x_936_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_935_, v_constName_931_, v___y_932_, v___y_933_);
lean_dec(v_ref_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_constName_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_constName_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v_env_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v___x_946_ = lean_st_ref_get(v___y_944_);
v_env_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref(v_env_947_);
lean_dec(v___x_946_);
v___x_948_ = 0;
lean_inc(v_constName_942_);
v___x_949_ = l_Lean_Environment_findConstVal_x3f(v_env_947_, v_constName_942_, v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_942_, v___y_943_, v___y_944_);
return v___x_950_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v___y_943_);
lean_dec(v_constName_942_);
v_val_951_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_val_951_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9___boxed(lean_object* v_constName_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_constName_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__10(lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
if (lean_obj_tag(v_a_964_) == 0)
{
lean_object* v___x_966_; 
v___x_966_ = l_List_reverse___redArg(v_a_965_);
return v___x_966_;
}
else
{
lean_object* v_head_967_; lean_object* v_tail_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_head_967_ = lean_ctor_get(v_a_964_, 0);
v_tail_968_ = lean_ctor_get(v_a_964_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v_a_964_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_tail_968_);
lean_inc(v_head_967_);
lean_dec(v_a_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_Lean_mkLevelParam(v_head_967_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v_a_965_);
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_a_965_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v_a_964_ = v_tail_968_;
v_a_965_ = v___x_974_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc(v_constName_978_);
v___x_982_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_constName_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_994_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_994_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_levelParams_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_levelParams_987_ = lean_ctor_get(v_a_983_, 1);
lean_inc(v_levelParams_987_);
lean_dec(v_a_983_);
v___x_988_ = lean_box(0);
v___x_989_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__10(v_levelParams_987_, v___x_988_);
v___x_990_ = l_Lean_mkConst(v_constName_978_, v___x_989_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_990_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_constName_978_);
v_a_995_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_982_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_982_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_1008_, lean_object* v_n_1009_, lean_object* v_expectedType_x3f_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
lean_inc_ref(v___y_1011_);
v___x_1014_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_1009_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_stx_1008_);
v___x_1018_ = l_Lean_LocalContext_empty;
v___x_1019_ = 0;
v___x_1020_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1018_);
lean_ctor_set(v___x_1020_, 2, v_expectedType_x3f_1010_);
lean_ctor_set(v___x_1020_, 3, v_a_1015_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*4, v___x_1019_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*4 + 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
v___x_1022_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1021_, v___y_1011_, v___y_1012_);
lean_dec_ref(v___y_1011_);
return v___x_1022_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___y_1011_);
lean_dec(v_expectedType_x3f_1010_);
lean_dec(v_stx_1008_);
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1014_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1014_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1031_, lean_object* v_n_1032_, lean_object* v_expectedType_x3f_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1031_, v_n_1032_, v_expectedType_x3f_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(lean_object* v_keys_1038_, lean_object* v_i_1039_, lean_object* v_k_1040_){
_start:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_array_get_size(v_keys_1038_);
v___x_1042_ = lean_nat_dec_lt(v_i_1039_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_dec(v_i_1039_);
return v___x_1042_;
}
else
{
lean_object* v_k_x27_1043_; uint8_t v___x_1044_; 
v_k_x27_1043_ = lean_array_fget_borrowed(v_keys_1038_, v_i_1039_);
v___x_1044_ = l_Lean_instBEqExtraModUse_beq(v_k_1040_, v_k_x27_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_i_1039_, v___x_1045_);
lean_dec(v_i_1039_);
v_i_1039_ = v___x_1046_;
goto _start;
}
else
{
lean_dec(v_i_1039_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_keys_1048_, lean_object* v_i_1049_, lean_object* v_k_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_1048_, v_i_1049_, v_k_1050_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_keys_1048_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; 
v___x_1053_ = ((size_t)5ULL);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_shift_left(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; 
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1058_ = lean_usize_sub(v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1059_, size_t v_x_1060_, lean_object* v_x_1061_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v_es_1062_; lean_object* v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v_j_1067_; lean_object* v___x_1068_; 
v_es_1062_ = lean_ctor_get(v_x_1059_, 0);
lean_inc_ref(v_es_1062_);
lean_dec_ref(v_x_1059_);
v___x_1063_ = lean_box(2);
v___x_1064_ = ((size_t)5ULL);
v___x_1065_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1066_ = lean_usize_land(v_x_1060_, v___x_1065_);
v_j_1067_ = lean_usize_to_nat(v___x_1066_);
v___x_1068_ = lean_array_get(v___x_1063_, v_es_1062_, v_j_1067_);
lean_dec(v_j_1067_);
lean_dec_ref(v_es_1062_);
switch(lean_obj_tag(v___x_1068_))
{
case 0:
{
lean_object* v_key_1069_; uint8_t v___x_1070_; 
v_key_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_key_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Lean_instBEqExtraModUse_beq(v_x_1061_, v_key_1069_);
lean_dec(v_key_1069_);
return v___x_1070_;
}
case 1:
{
lean_object* v_node_1071_; size_t v___x_1072_; 
v_node_1071_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_node_1071_);
lean_dec_ref(v___x_1068_);
v___x_1072_ = lean_usize_shift_right(v_x_1060_, v___x_1064_);
v_x_1059_ = v_node_1071_;
v_x_1060_ = v___x_1072_;
goto _start;
}
default: 
{
uint8_t v___x_1074_; 
v___x_1074_ = 0;
return v___x_1074_;
}
}
}
else
{
lean_object* v_ks_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_ks_1075_ = lean_ctor_get(v_x_1059_, 0);
lean_inc_ref(v_ks_1075_);
lean_dec_ref(v_x_1059_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_ks_1075_, v___x_1076_, v_x_1061_);
lean_dec_ref(v_ks_1075_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
size_t v_x_6906__boxed_1081_; uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_x_6906__boxed_1081_ = lean_unbox_usize(v_x_1079_);
lean_dec(v_x_1079_);
v_res_1082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1078_, v_x_6906__boxed_1081_, v_x_1080_);
lean_dec_ref(v_x_1080_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
uint64_t v___x_1086_; size_t v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = l_Lean_instHashableExtraModUse_hash(v_x_1085_);
v___x_1087_ = lean_uint64_to_usize(v___x_1086_);
v___x_1088_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1084_, v___x_1087_, v_x_1085_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1089_, v_x_1090_);
lean_dec_ref(v_x_1090_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_options_1099_; uint8_t v_hasTrace_1100_; 
v_options_1099_ = lean_ctor_get(v___y_1097_, 2);
v_hasTrace_1100_ = lean_ctor_get_uint8(v_options_1099_, sizeof(void*)*1);
if (v_hasTrace_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_cls_1096_);
v___x_1101_ = lean_box(v_hasTrace_1100_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v_inheritedTraceOptions_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_inheritedTraceOptions_1103_ = lean_ctor_get(v___y_1097_, 13);
v___x_1104_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_1105_ = l_Lean_Name_append(v___x_1104_, v_cls_1096_);
v___x_1106_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1103_, v_options_1099_, v___x_1105_);
lean_dec(v___x_1105_);
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1109_, v___y_1110_);
lean_dec_ref(v___y_1110_);
return v_res_1112_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1113_; double v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_float_of_nat(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(lean_object* v_cls_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_ref_1123_; lean_object* v___x_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1169_; 
v_ref_1123_ = lean_ctor_get(v___y_1120_, 5);
v___x_1124_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1119_, v___y_1120_, v___y_1121_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1169_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1169_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v_traceState_1130_; lean_object* v_env_1131_; lean_object* v_nextMacroScope_1132_; lean_object* v_ngen_1133_; lean_object* v_auxDeclNGen_1134_; lean_object* v_cache_1135_; lean_object* v_messages_1136_; lean_object* v_infoState_1137_; lean_object* v_snapshotTasks_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1168_; 
v___x_1129_ = lean_st_ref_take(v___y_1121_);
v_traceState_1130_ = lean_ctor_get(v___x_1129_, 4);
v_env_1131_ = lean_ctor_get(v___x_1129_, 0);
v_nextMacroScope_1132_ = lean_ctor_get(v___x_1129_, 1);
v_ngen_1133_ = lean_ctor_get(v___x_1129_, 2);
v_auxDeclNGen_1134_ = lean_ctor_get(v___x_1129_, 3);
v_cache_1135_ = lean_ctor_get(v___x_1129_, 5);
v_messages_1136_ = lean_ctor_get(v___x_1129_, 6);
v_infoState_1137_ = lean_ctor_get(v___x_1129_, 7);
v_snapshotTasks_1138_ = lean_ctor_get(v___x_1129_, 8);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1140_ = v___x_1129_;
v_isShared_1141_ = v_isSharedCheck_1168_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_snapshotTasks_1138_);
lean_inc(v_infoState_1137_);
lean_inc(v_messages_1136_);
lean_inc(v_cache_1135_);
lean_inc(v_traceState_1130_);
lean_inc(v_auxDeclNGen_1134_);
lean_inc(v_ngen_1133_);
lean_inc(v_nextMacroScope_1132_);
lean_inc(v_env_1131_);
lean_dec(v___x_1129_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1168_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint64_t v_tid_1142_; lean_object* v_traces_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_tid_1142_ = lean_ctor_get_uint64(v_traceState_1130_, sizeof(void*)*1);
v_traces_1143_ = lean_ctor_get(v_traceState_1130_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_traceState_1130_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v_traceState_1130_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_traces_1143_);
lean_dec(v_traceState_1130_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; double v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__0);
v___x_1149_ = 0;
v___x_1150_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1));
v___x_1151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1151_, 0, v_cls_1118_);
lean_ctor_set(v___x_1151_, 1, v___x_1147_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
lean_ctor_set_float(v___x_1151_, sizeof(void*)*3, v___x_1148_);
lean_ctor_set_float(v___x_1151_, sizeof(void*)*3 + 8, v___x_1148_);
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*3 + 16, v___x_1149_);
v___x_1152_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__2));
v___x_1153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v_a_1125_);
lean_ctor_set(v___x_1153_, 2, v___x_1152_);
lean_inc(v_ref_1123_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_ref_1123_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_PersistentArray_push___redArg(v_traces_1143_, v___x_1154_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1155_);
v___x_1157_ = v___x_1145_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1155_);
lean_ctor_set_uint64(v_reuseFailAlloc_1166_, sizeof(void*)*1, v_tid_1142_);
v___x_1157_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 4, v___x_1157_);
v___x_1159_ = v___x_1140_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_env_1131_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_nextMacroScope_1132_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_ngen_1133_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_auxDeclNGen_1134_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 5, v_cache_1135_);
lean_ctor_set(v_reuseFailAlloc_1165_, 6, v_messages_1136_);
lean_ctor_set(v_reuseFailAlloc_1165_, 7, v_infoState_1137_);
lean_ctor_set(v_reuseFailAlloc_1165_, 8, v_snapshotTasks_1138_);
v___x_1159_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = lean_st_ref_set(v___y_1121_, v___x_1159_);
v___x_1161_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1161_);
v___x_1163_ = v___x_1127_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_1170_, lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(v_cls_1170_, v_msg_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1179_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1180_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1181_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3___closed__1));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1207_, uint8_t v_isMeta_1208_, lean_object* v_hint_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v_env_1214_; uint8_t v_isExporting_1215_; lean_object* v___x_1216_; lean_object* v_env_1217_; lean_object* v___x_1218_; lean_object* v_entry_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___y_1224_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1213_ = lean_st_ref_get(v___y_1211_);
v_env_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc_ref(v_env_1214_);
lean_dec(v___x_1213_);
v_isExporting_1215_ = lean_ctor_get_uint8(v_env_1214_, sizeof(void*)*8);
lean_dec_ref(v_env_1214_);
v___x_1216_ = lean_st_ref_get(v___y_1211_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1207_);
v_entry_1219_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1219_, 0, v_mod_1207_);
lean_ctor_set_uint8(v_entry_1219_, sizeof(void*)*1, v_isExporting_1215_);
lean_ctor_set_uint8(v_entry_1219_, sizeof(void*)*1 + 1, v_isMeta_1208_);
v___x_1220_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1221_ = lean_box(1);
v___x_1222_ = lean_box(0);
v___x_1249_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1218_, v___x_1220_, v_env_1217_, v___x_1221_, v___x_1222_);
v___x_1250_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1249_, v_entry_1219_);
if (v___x_1250_ == 0)
{
lean_object* v_cls_1251_; lean_object* v___x_1252_; lean_object* v_a_1253_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v___x_1273_; 
v_cls_1251_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1252_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1251_, v___y_1210_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1252_);
v___x_1273_ = lean_unbox(v_a_1253_);
lean_dec(v_a_1253_);
if (v___x_1273_ == 0)
{
lean_dec(v_hint_1209_);
lean_dec(v_mod_1207_);
v___y_1224_ = v___y_1211_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1274_; lean_object* v___y_1276_; 
v___x_1274_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1215_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1276_ = v___x_1283_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1276_ = v___x_1284_;
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = l_Lean_stringToMessageData(v___y_1276_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1274_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
if (v_isMeta_1208_ == 0)
{
lean_object* v___x_1281_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1260_ = v___x_1280_;
v___y_1261_ = v___x_1281_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1260_ = v___x_1280_;
v___y_1261_ = v___x_1282_;
goto v___jp_1259_;
}
}
}
v___jp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1255_);
lean_ctor_set(v___x_1257_, 1, v___y_1256_);
v___x_1258_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__3(v_cls_1251_, v___x_1257_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_dec_ref(v___x_1258_);
v___y_1224_ = v___y_1211_;
goto v___jp_1223_;
}
else
{
lean_dec_ref(v_entry_1219_);
return v___x_1258_;
}
}
v___jp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1262_ = l_Lean_stringToMessageData(v___y_1261_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1260_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_MessageData_ofName(v_mod_1207_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_Name_isAnonymous(v_hint_1209_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1270_ = l_Lean_MessageData_ofName(v_hint_1209_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___y_1255_ = v___x_1267_;
v___y_1256_ = v___x_1271_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_hint_1209_);
v___x_1272_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1255_ = v___x_1267_;
v___y_1256_ = v___x_1272_;
goto v___jp_1254_;
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec_ref(v_entry_1219_);
lean_dec(v_hint_1209_);
lean_dec(v_mod_1207_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; lean_object* v_toEnvExtension_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_traceState_1231_; lean_object* v_messages_1232_; lean_object* v_infoState_1233_; lean_object* v_snapshotTasks_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1247_; 
v___x_1225_ = lean_st_ref_take(v___y_1224_);
v_toEnvExtension_1226_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_toEnvExtension_1226_);
v_env_1227_ = lean_ctor_get(v___x_1225_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1225_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1225_, 3);
v_traceState_1231_ = lean_ctor_get(v___x_1225_, 4);
v_messages_1232_ = lean_ctor_get(v___x_1225_, 6);
v_infoState_1233_ = lean_ctor_get(v___x_1225_, 7);
v_snapshotTasks_1234_ = lean_ctor_get(v___x_1225_, 8);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1225_, 5);
lean_dec(v_unused_1248_);
v___x_1236_ = v___x_1225_;
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snapshotTasks_1234_);
lean_inc(v_infoState_1233_);
lean_inc(v_messages_1232_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1225_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_asyncMode_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v_asyncMode_1238_ = lean_ctor_get(v_toEnvExtension_1226_, 2);
lean_inc(v_asyncMode_1238_);
lean_dec_ref(v_toEnvExtension_1226_);
v___x_1239_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1220_, v_env_1227_, v_entry_1219_, v_asyncMode_1238_, v___x_1222_);
lean_dec(v_asyncMode_1238_);
v___x_1240_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 5, v___x_1240_);
lean_ctor_set(v___x_1236_, 0, v___x_1239_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_traceState_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_messages_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_infoState_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_snapshotTasks_1234_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_st_ref_set(v___y_1224_, v___x_1242_);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1287_, lean_object* v_isMeta_1288_, lean_object* v_hint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v_isMeta_boxed_1293_; lean_object* v_res_1294_; 
v_isMeta_boxed_1293_ = lean_unbox(v_isMeta_1288_);
v_res_1294_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1287_, v_isMeta_boxed_1293_, v_hint_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1295_, lean_object* v_declName_1296_, lean_object* v_as_1297_, size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_declName_1296_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_b_1300_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v_modules_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v_toImport_1311_; lean_object* v_module_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1306_ = l_Lean_Environment_header(v___x_1295_);
v_modules_1307_ = lean_ctor_get(v___x_1306_, 3);
lean_inc_ref(v_modules_1307_);
lean_dec_ref(v___x_1306_);
v___x_1308_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1309_ = lean_array_uget_borrowed(v_as_1297_, v_i_1299_);
v___x_1310_ = lean_array_get(v___x_1308_, v_modules_1307_, v_a_1309_);
lean_dec_ref(v_modules_1307_);
v_toImport_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_toImport_1311_);
lean_dec(v___x_1310_);
v_module_1312_ = lean_ctor_get(v_toImport_1311_, 0);
lean_inc(v_module_1312_);
lean_dec_ref(v_toImport_1311_);
v___x_1313_ = 0;
lean_inc(v_declName_1296_);
v___x_1314_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1312_, v___x_1313_, v_declName_1296_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; 
lean_dec_ref(v___x_1314_);
v___x_1315_ = lean_box(0);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1299_, v___x_1316_);
v_i_1299_ = v___x_1317_;
v_b_1300_ = v___x_1315_;
goto _start;
}
else
{
lean_dec(v_declName_1296_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1319_, lean_object* v_declName_1320_, lean_object* v_as_1321_, lean_object* v_sz_1322_, lean_object* v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
size_t v_sz_boxed_1328_; size_t v_i_boxed_1329_; lean_object* v_res_1330_; 
v_sz_boxed_1328_ = lean_unbox_usize(v_sz_1322_);
lean_dec(v_sz_1322_);
v_i_boxed_1329_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1319_, v_declName_1320_, v_as_1321_, v_sz_boxed_1328_, v_i_boxed_1329_, v_b_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v_as_1321_);
lean_dec_ref(v___x_1319_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(lean_object* v_a_1331_, lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_box(0);
return v___x_1333_;
}
else
{
lean_object* v_key_1334_; lean_object* v_value_1335_; lean_object* v_tail_1336_; uint8_t v___x_1337_; 
v_key_1334_ = lean_ctor_get(v_x_1332_, 0);
v_value_1335_ = lean_ctor_get(v_x_1332_, 1);
v_tail_1336_ = lean_ctor_get(v_x_1332_, 2);
v___x_1337_ = lean_name_eq(v_key_1334_, v_a_1331_);
if (v___x_1337_ == 0)
{
v_x_1332_ = v_tail_1336_;
goto _start;
}
else
{
lean_object* v___x_1339_; 
lean_inc(v_value_1335_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_value_1335_);
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1340_, v_x_1341_);
lean_dec(v_x_1341_);
lean_dec(v_a_1340_);
return v_res_1342_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1343_; uint64_t v___x_1344_; 
v___x_1343_ = lean_unsigned_to_nat(1723u);
v___x_1344_ = lean_uint64_of_nat(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_buckets_1347_; lean_object* v___x_1348_; uint64_t v___y_1350_; 
v_buckets_1347_ = lean_ctor_get(v_m_1345_, 1);
v___x_1348_ = lean_array_get_size(v_buckets_1347_);
if (lean_obj_tag(v_a_1346_) == 0)
{
uint64_t v___x_1364_; 
v___x_1364_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1350_ = v___x_1364_;
goto v___jp_1349_;
}
else
{
uint64_t v_hash_1365_; 
v_hash_1365_ = lean_ctor_get_uint64(v_a_1346_, sizeof(void*)*2);
v___y_1350_ = v_hash_1365_;
goto v___jp_1349_;
}
v___jp_1349_:
{
uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v_fold_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1351_ = 32ULL;
v___x_1352_ = lean_uint64_shift_right(v___y_1350_, v___x_1351_);
v_fold_1353_ = lean_uint64_xor(v___y_1350_, v___x_1352_);
v___x_1354_ = 16ULL;
v___x_1355_ = lean_uint64_shift_right(v_fold_1353_, v___x_1354_);
v___x_1356_ = lean_uint64_xor(v_fold_1353_, v___x_1355_);
v___x_1357_ = lean_uint64_to_usize(v___x_1356_);
v___x_1358_ = lean_usize_of_nat(v___x_1348_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_sub(v___x_1358_, v___x_1359_);
v___x_1361_ = lean_usize_land(v___x_1357_, v___x_1360_);
v___x_1362_ = lean_array_uget_borrowed(v_buckets_1347_, v___x_1361_);
v___x_1363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1346_, v___x_1362_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_m_1366_);
return v_res_1368_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1372_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1373_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1372_, v___x_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1376_, uint8_t v_isMeta_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_env_1385_; lean_object* v___y_1387_; lean_object* v___x_1400_; 
v___x_1381_ = lean_st_ref_get(v___y_1379_);
v_env_1385_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref(v_env_1385_);
lean_dec(v___x_1381_);
v___x_1400_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1385_, v_declName_1376_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec_ref(v_env_1385_);
lean_dec(v_declName_1376_);
goto v___jp_1382_;
}
else
{
lean_object* v_val_1401_; lean_object* v___x_1402_; lean_object* v_modules_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = l_Lean_Environment_header(v_env_1385_);
v_modules_1403_ = lean_ctor_get(v___x_1402_, 3);
lean_inc_ref(v_modules_1403_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = lean_array_get_size(v_modules_1403_);
v___x_1405_ = lean_nat_dec_lt(v_val_1401_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_modules_1403_);
lean_dec(v_val_1401_);
lean_dec_ref(v_env_1385_);
lean_dec(v_declName_1376_);
goto v___jp_1382_;
}
else
{
lean_object* v___x_1406_; lean_object* v_env_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___y_1411_; 
v___x_1406_ = lean_st_ref_get(v___y_1379_);
v_env_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1407_);
lean_dec(v___x_1406_);
v___x_1408_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1409_ = lean_array_fget(v_modules_1403_, v_val_1401_);
lean_dec(v_val_1401_);
lean_dec_ref(v_modules_1403_);
if (v_isMeta_1377_ == 0)
{
lean_dec_ref(v_env_1407_);
v___y_1411_ = v_isMeta_1377_;
goto v___jp_1410_;
}
else
{
uint8_t v___x_1422_; 
lean_inc(v_declName_1376_);
v___x_1422_ = l_Lean_isMarkedMeta(v_env_1407_, v_declName_1376_);
if (v___x_1422_ == 0)
{
v___y_1411_ = v_isMeta_1377_;
goto v___jp_1410_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
v___y_1411_ = v___x_1423_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v_toImport_1412_; lean_object* v_module_1413_; lean_object* v___x_1414_; 
v_toImport_1412_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_toImport_1412_);
lean_dec(v___x_1409_);
v_module_1413_ = lean_ctor_get(v_toImport_1412_, 0);
lean_inc(v_module_1413_);
lean_dec_ref(v_toImport_1412_);
lean_inc(v_declName_1376_);
v___x_1414_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1413_, v___y_1411_, v_declName_1376_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v___x_1414_);
v___x_1415_ = l_Lean_indirectModUseExt;
v___x_1416_ = lean_box(1);
v___x_1417_ = lean_box(0);
lean_inc_ref(v_env_1385_);
v___x_1418_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1408_, v___x_1415_, v_env_1385_, v___x_1416_, v___x_1417_);
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1418_, v_declName_1376_);
lean_dec(v___x_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1387_ = v___x_1420_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v___x_1419_);
v___y_1387_ = v_val_1421_;
goto v___jp_1386_;
}
}
else
{
lean_dec_ref(v_env_1385_);
lean_dec(v_declName_1376_);
return v___x_1414_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
v___jp_1386_:
{
lean_object* v___x_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v___x_1388_ = lean_box(0);
v_sz_1389_ = lean_array_size(v___y_1387_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1385_, v_declName_1376_, v___y_1387_, v_sz_1389_, v___x_1390_, v___x_1388_, v___y_1378_, v___y_1379_);
lean_dec_ref(v___y_1387_);
lean_dec_ref(v_env_1385_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1399_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1388_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1388_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1424_, lean_object* v_isMeta_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_isMeta_boxed_1429_; lean_object* v_res_1430_; 
v_isMeta_boxed_1429_ = lean_unbox(v_isMeta_1425_);
v_res_1430_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1424_, v_isMeta_boxed_1429_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1431_, uint8_t v_x_1432_, lean_object* v_stx_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
lean_inc_ref(v___y_1434_);
lean_inc(v_stx_1433_);
v___x_1437_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1431_, v_stx_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1490_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1490_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1490_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v_env_1443_; uint8_t v___x_1444_; uint8_t v___x_1445_; 
v___x_1442_ = lean_st_ref_get(v___y_1435_);
v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = 1;
lean_inc(v_a_1438_);
v___x_1445_ = l_Lean_Environment_contains(v_env_1443_, v_a_1438_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref(v___y_1434_);
lean_dec(v_stx_1433_);
if (v_isShared_1441_ == 0)
{
v___x_1447_ = v___x_1440_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1438_);
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
uint8_t v___x_1449_; lean_object* v___x_1450_; 
lean_del_object(v___x_1440_);
v___x_1449_ = 0;
lean_inc(v_a_1438_);
v___x_1450_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1438_, v___x_1449_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1450_, 0);
lean_dec(v_unused_1481_);
v___x_1452_ = v___x_1450_;
v_isShared_1453_ = v_isSharedCheck_1480_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1450_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1480_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v_infoState_1455_; uint8_t v_enabled_1456_; 
v___x_1454_ = lean_st_ref_get(v___y_1435_);
v_infoState_1455_ = lean_ctor_get(v___x_1454_, 7);
lean_inc_ref(v_infoState_1455_);
lean_dec(v___x_1454_);
v_enabled_1456_ = lean_ctor_get_uint8(v_infoState_1455_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1455_);
if (v_enabled_1456_ == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref(v___y_1434_);
lean_dec(v_stx_1433_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_a_1438_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1438_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_del_object(v___x_1452_);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = l_Lean_Syntax_getArg(v_stx_1433_, v___x_1460_);
lean_dec(v_stx_1433_);
v___x_1462_ = lean_box(0);
lean_inc(v_a_1438_);
v___x_1463_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1461_, v_a_1438_, v___x_1462_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1463_, 0);
lean_dec(v_unused_1471_);
v___x_1465_ = v___x_1463_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v___x_1463_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v_a_1438_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1438_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1438_);
v_a_1472_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1463_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1463_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1438_);
lean_dec_ref(v___y_1434_);
lean_dec(v_stx_1433_);
v_a_1482_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1450_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1450_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1434_);
lean_dec(v_stx_1433_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1491_, lean_object* v_x_1492_, lean_object* v_stx_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v_x_7518__boxed_1497_; lean_object* v_res_1498_; 
v_x_7518__boxed_1497_ = lean_unbox(v_x_1492_);
v_res_1498_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1491_, v_x_7518__boxed_1497_, v_stx_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1501_, lean_object* v_attrName_1502_, lean_object* v_parserNamespace_1503_, lean_object* v_typeName_1504_, lean_object* v_kind_1505_, lean_object* v_attrDeclName_1506_){
_start:
{
lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___f_1508_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1509_, 0, v_parserNamespace_1503_);
v___x_1510_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1511_ = lean_string_append(v_kind_1505_, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1512_, 0, v_attrBuiltinName_1501_);
lean_ctor_set(v___x_1512_, 1, v_attrName_1502_);
lean_ctor_set(v___x_1512_, 2, v___x_1511_);
lean_ctor_set(v___x_1512_, 3, v_typeName_1504_);
lean_ctor_set(v___x_1512_, 4, v___f_1509_);
lean_ctor_set(v___x_1512_, 5, v___f_1508_);
v___x_1513_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1512_, v_attrDeclName_1506_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1514_, lean_object* v_attrName_1515_, lean_object* v_parserNamespace_1516_, lean_object* v_typeName_1517_, lean_object* v_kind_1518_, lean_object* v_attrDeclName_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1514_, v_attrName_1515_, v_parserNamespace_1516_, v_typeName_1517_, v_kind_1518_, v_attrDeclName_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1522_, lean_object* v_attrBuiltinName_1523_, lean_object* v_attrName_1524_, lean_object* v_parserNamespace_1525_, lean_object* v_typeName_1526_, lean_object* v_kind_1527_, lean_object* v_attrDeclName_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1523_, v_attrName_1524_, v_parserNamespace_1525_, v_typeName_1526_, v_kind_1527_, v_attrDeclName_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1531_, lean_object* v_attrBuiltinName_1532_, lean_object* v_attrName_1533_, lean_object* v_parserNamespace_1534_, lean_object* v_typeName_1535_, lean_object* v_kind_1536_, lean_object* v_attrDeclName_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1531_, v_attrBuiltinName_1532_, v_attrName_1533_, v_parserNamespace_1534_, v_typeName_1535_, v_kind_1536_, v_attrDeclName_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___redArg(v_cls_1540_, v___y_1541_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1550_, lean_object* v_m_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1551_, v_a_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1554_, lean_object* v_m_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1554_, v_m_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_m_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12(lean_object* v_t_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___redArg(v_t_1558_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12___boxed(lean_object* v_t_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__12(v_t_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1569_, v_x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1572_, v_x_1573_, v_x_1574_);
lean_dec_ref(v_x_1574_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___redArg(v_a_1578_, v_x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1581_, lean_object* v_a_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__6(v_00_u03b2_1581_, v_a_1582_, v_x_1583_);
lean_dec(v_x_1583_);
lean_dec(v_a_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1585_, lean_object* v_x_1586_, size_t v_x_1587_, lean_object* v_x_1588_){
_start:
{
uint8_t v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1586_, v_x_1587_, v_x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
size_t v_x_7699__boxed_1594_; uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_x_7699__boxed_1594_ = lean_unbox_usize(v_x_1592_);
lean_dec(v_x_1592_);
v_res_1595_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1590_, v_x_1591_, v_x_7699__boxed_1594_, v_x_1593_);
lean_dec_ref(v_x_1593_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_1597_, lean_object* v_constName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___redArg(v_constName_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_constName_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11(v_00_u03b1_1603_, v_constName_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10(lean_object* v_00_u03b2_1609_, lean_object* v_keys_1610_, lean_object* v_vals_1611_, lean_object* v_heq_1612_, lean_object* v_i_1613_, lean_object* v_k_1614_){
_start:
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___redArg(v_keys_1610_, v_i_1613_, v_k_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_keys_1617_, lean_object* v_vals_1618_, lean_object* v_heq_1619_, lean_object* v_i_1620_, lean_object* v_k_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__10(v_00_u03b2_1616_, v_keys_1617_, v_vals_1618_, v_heq_1619_, v_i_1620_, v_k_1621_);
lean_dec_ref(v_k_1621_);
lean_dec_ref(v_vals_1618_);
lean_dec_ref(v_keys_1617_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15(lean_object* v_00_u03b1_1624_, lean_object* v_ref_1625_, lean_object* v_constName_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___redArg(v_ref_1625_, v_constName_1626_, v___y_1627_, v___y_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_ref_1632_, lean_object* v_constName_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15(v_00_u03b1_1631_, v_ref_1632_, v_constName_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec(v_ref_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17(lean_object* v_00_u03b1_1638_, lean_object* v_ref_1639_, lean_object* v_msg_1640_, lean_object* v_declHint_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___redArg(v_ref_1639_, v_msg_1640_, v_declHint_1641_, v___y_1642_, v___y_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17___boxed(lean_object* v_00_u03b1_1646_, lean_object* v_ref_1647_, lean_object* v_msg_1648_, lean_object* v_declHint_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17(v_00_u03b1_1646_, v_ref_1647_, v_msg_1648_, v_declHint_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec(v_ref_1647_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_1654_, lean_object* v_declHint_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_1654_, v_declHint_1655_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__18_spec__19(v_msg_1660_, v_declHint_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_1666_, lean_object* v_ref_1667_, lean_object* v_msg_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___redArg(v_ref_1667_, v_msg_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_ref_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9_spec__11_spec__15_spec__17_spec__19(v_00_u03b1_1673_, v_ref_1674_, v_msg_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec(v_ref_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1690_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1692_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1693_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1694_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1695_ = lean_box(0);
v___x_1696_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1697_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1692_, v___x_1694_, v___x_1695_, v___x_1696_, v___x_1693_, v_ref_1690_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1708_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1714_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1715_ = l_Lean_addBuiltinDocString(v___x_1713_, v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1745_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1746_ = l_Lean_addBuiltinDeclarationRanges(v___x_1744_, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1749_, lean_object* v_a_1750_, lean_object* v_____r_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_declName_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1765_; 
v_declName_1754_ = lean_ctor_get(v_toOLeanEntry_1749_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_toOLeanEntry_1749_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v_toOLeanEntry_1749_, 0);
lean_dec(v_unused_1766_);
v___x_1756_ = v_toOLeanEntry_1749_;
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_declName_1754_);
lean_dec(v_toOLeanEntry_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1765_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_a_1750_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1758_);
lean_ctor_set(v___x_1756_, 0, v_declName_1754_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_declName_1754_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___y_1753_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1767_, lean_object* v_a_1768_, lean_object* v_____r_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1767_, v_a_1768_, v_____r_1769_, v___y_1770_, v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1776_, lean_object* v_as_x27_1777_, lean_object* v_b_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
if (lean_obj_tag(v_as_x27_1777_) == 0)
{
lean_object* v___x_1781_; 
lean_dec(v_stx_1776_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_b_1778_);
lean_ctor_set(v___x_1781_, 1, v___y_1780_);
return v___x_1781_;
}
else
{
lean_object* v_head_1782_; lean_object* v_tail_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_b_1778_);
v_head_1782_ = lean_ctor_get(v_as_x27_1777_, 0);
v_tail_1783_ = lean_ctor_get(v_as_x27_1777_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_as_x27_1777_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1785_ = v_as_x27_1777_;
v_isShared_1786_ = v_isSharedCheck_1861_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_tail_1783_);
lean_inc(v_head_1782_);
lean_dec(v_as_x27_1777_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1861_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_toOLeanEntry_1787_; uint8_t v_isBuiltin_1788_; lean_object* v_value_1789_; lean_object* v_macroScope_1790_; lean_object* v_traceMsgs_1791_; lean_object* v_expandedMacroDecls_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1860_; 
v_toOLeanEntry_1787_ = lean_ctor_get(v_head_1782_, 0);
lean_inc_ref(v_toOLeanEntry_1787_);
v_isBuiltin_1788_ = lean_ctor_get_uint8(v_head_1782_, sizeof(void*)*2);
v_value_1789_ = lean_ctor_get(v_head_1782_, 1);
lean_inc(v_value_1789_);
lean_dec(v_head_1782_);
v_macroScope_1790_ = lean_ctor_get(v___y_1780_, 0);
v_traceMsgs_1791_ = lean_ctor_get(v___y_1780_, 1);
v_expandedMacroDecls_1792_ = lean_ctor_get(v___y_1780_, 2);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___y_1780_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1794_ = v___y_1780_;
v_isShared_1795_ = v_isSharedCheck_1860_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_expandedMacroDecls_1792_);
lean_inc(v_traceMsgs_1791_);
lean_inc(v_macroScope_1790_);
lean_dec(v___y_1780_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1860_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_methods_1796_; lean_object* v_quotContext_1797_; lean_object* v_currRecDepth_1798_; lean_object* v_maxRecDepth_1799_; lean_object* v_ref_1800_; lean_object* v___x_1801_; lean_object* v_a_1803_; lean_object* v_a_1804_; lean_object* v___x_1808_; lean_object* v_a_1810_; lean_object* v_a_1811_; lean_object* v___y_1825_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v_methods_1796_ = lean_ctor_get(v___y_1779_, 0);
v_quotContext_1797_ = lean_ctor_get(v___y_1779_, 1);
v_currRecDepth_1798_ = lean_ctor_get(v___y_1779_, 3);
v_maxRecDepth_1799_ = lean_ctor_get(v___y_1779_, 4);
v_ref_1800_ = lean_ctor_get(v___y_1779_, 5);
v___x_1801_ = lean_box(0);
v___x_1808_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_nat_add(v_macroScope_1790_, v___x_1831_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1832_);
v___x_1834_ = v___x_1794_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_traceMsgs_1791_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_expandedMacroDecls_1792_);
v___x_1834_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1833_;
}
v___jp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_a_1803_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1801_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_a_1804_);
return v___x_1807_;
}
v___jp_1809_:
{
if (lean_obj_tag(v_a_1810_) == 1)
{
lean_dec_ref(v_toOLeanEntry_1787_);
v_as_x27_1777_ = v_tail_1783_;
v_b_1778_ = v___x_1808_;
v___y_1780_ = v_a_1811_;
goto _start;
}
else
{
lean_object* v_declName_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_tail_1783_);
lean_dec(v_stx_1776_);
v_declName_1813_ = lean_ctor_get(v_toOLeanEntry_1787_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_toOLeanEntry_1787_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_toOLeanEntry_1787_, 0);
lean_dec(v_unused_1823_);
v___x_1815_ = v_toOLeanEntry_1787_;
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_declName_1813_);
lean_dec(v_toOLeanEntry_1787_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_a_1810_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v___x_1817_);
lean_ctor_set(v___x_1815_, 0, v_declName_1813_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_declName_1813_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
v_a_1803_ = v___x_1820_;
v_a_1804_ = v_a_1811_;
goto v___jp_1802_;
}
}
}
}
v___jp_1824_:
{
lean_object* v_a_1826_; 
v_a_1826_ = lean_ctor_get(v___y_1825_, 0);
if (lean_obj_tag(v_a_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v_a_1828_; 
lean_inc_ref(v_a_1826_);
lean_dec(v_tail_1783_);
lean_dec(v_stx_1776_);
v_a_1827_ = lean_ctor_get(v___y_1825_, 1);
lean_inc(v_a_1827_);
lean_dec_ref(v___y_1825_);
v_a_1828_ = lean_ctor_get(v_a_1826_, 0);
lean_inc(v_a_1828_);
lean_dec_ref(v_a_1826_);
v_a_1803_ = v_a_1828_;
v_a_1804_ = v_a_1827_;
goto v___jp_1802_;
}
else
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___y_1825_, 1);
lean_inc(v_a_1829_);
lean_dec_ref(v___y_1825_);
v_as_x27_1777_ = v_tail_1783_;
v_b_1778_ = v___x_1808_;
v___y_1780_ = v_a_1829_;
goto _start;
}
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_inc(v_ref_1800_);
lean_inc(v_maxRecDepth_1799_);
lean_inc(v_currRecDepth_1798_);
lean_inc(v_quotContext_1797_);
lean_inc(v_methods_1796_);
v___x_1835_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1835_, 0, v_methods_1796_);
lean_ctor_set(v___x_1835_, 1, v_quotContext_1797_);
lean_ctor_set(v___x_1835_, 2, v_macroScope_1790_);
lean_ctor_set(v___x_1835_, 3, v_currRecDepth_1798_);
lean_ctor_set(v___x_1835_, 4, v_maxRecDepth_1799_);
lean_ctor_set(v___x_1835_, 5, v_ref_1800_);
lean_inc(v_stx_1776_);
v___x_1836_ = lean_apply_3(v_value_1789_, v_stx_1776_, v___x_1835_, v___x_1834_);
if (lean_obj_tag(v___x_1836_) == 0)
{
if (v_isBuiltin_1788_ == 0)
{
lean_object* v_a_1837_; lean_object* v_a_1838_; lean_object* v_macroScope_1839_; lean_object* v_traceMsgs_1840_; lean_object* v_expandedMacroDecls_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1853_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_a_1837_);
v_a_1838_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1836_);
v_macroScope_1839_ = lean_ctor_get(v_a_1837_, 0);
v_traceMsgs_1840_ = lean_ctor_get(v_a_1837_, 1);
v_expandedMacroDecls_1841_ = lean_ctor_get(v_a_1837_, 2);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1843_ = v_a_1837_;
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_expandedMacroDecls_1841_);
lean_inc(v_traceMsgs_1840_);
lean_inc(v_macroScope_1839_);
lean_dec(v_a_1837_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_declName_1845_; lean_object* v___x_1847_; 
v_declName_1845_ = lean_ctor_get(v_toOLeanEntry_1787_, 1);
lean_inc(v_declName_1845_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v_expandedMacroDecls_1841_);
lean_ctor_set(v___x_1785_, 0, v_declName_1845_);
v___x_1847_ = v___x_1785_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_declName_1845_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_expandedMacroDecls_1841_);
v___x_1847_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 2, v___x_1847_);
v___x_1849_ = v___x_1843_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_macroScope_1839_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_traceMsgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1787_, v_a_1838_, v___x_1801_, v___y_1779_, v___x_1849_);
v___y_1825_ = v___x_1850_;
goto v___jp_1824_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v_a_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1785_);
v_a_1854_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1854_);
v_a_1855_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1836_);
v___x_1856_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1787_, v_a_1854_, v___x_1801_, v___y_1779_, v_a_1855_);
v___y_1825_ = v___x_1856_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v_a_1858_; 
lean_del_object(v___x_1785_);
v_a_1857_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1857_);
v_a_1858_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1836_);
v_a_1810_ = v_a_1857_;
v_a_1811_ = v_a_1858_;
goto v___jp_1809_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1862_, lean_object* v_as_x27_1863_, lean_object* v_b_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1862_, v_as_x27_1863_, v_b_1864_, v___y_1865_, v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1868_, lean_object* v_stx_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v_fst_1879_; 
v___x_1872_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1869_);
v___x_1873_ = l_Lean_Syntax_getKind(v_stx_1869_);
v___x_1874_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1872_, v_env_1868_, v___x_1873_);
lean_dec(v___x_1873_);
v___x_1875_ = lean_box(0);
v___x_1876_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1877_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1869_, v___x_1874_, v___x_1876_, v_a_1870_, v_a_1871_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
v_fst_1879_ = lean_ctor_get(v_a_1878_, 0);
lean_inc(v_fst_1879_);
lean_dec(v_a_1878_);
if (lean_obj_tag(v_fst_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1888_);
v___x_1882_ = v___x_1877_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1875_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_a_1889_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1898_);
v___x_1891_ = v___x_1877_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1877_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_val_1893_; lean_object* v___x_1895_; 
v_val_1893_ = lean_ctor_get(v_fst_1879_, 0);
lean_inc(v_val_1893_);
lean_dec_ref(v_fst_1879_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_val_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_val_1893_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_a_1889_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1899_, lean_object* v_stx_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1899_, v_stx_1900_, v_a_1901_, v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1904_, lean_object* v_as_1905_, lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v_a_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1904_, v_as_x27_1906_, v_b_1907_, v___y_1909_, v___y_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1912_, lean_object* v_as_1913_, lean_object* v_as_x27_1914_, lean_object* v_b_1915_, lean_object* v_a_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1912_, v_as_1913_, v_as_x27_1914_, v_b_1915_, v_a_1916_, v___y_1917_, v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v_as_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1920_, lean_object* v_inst_1921_, lean_object* v_s_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_apply_1(v_setNextMacroScope_1920_, v_s_1922_);
v___x_1924_ = lean_apply_2(v_inst_1921_, lean_box(0), v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_){
_start:
{
lean_object* v_getNextMacroScope_1928_; lean_object* v_setNextMacroScope_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1938_; 
v_getNextMacroScope_1928_ = lean_ctor_get(v_inst_1927_, 1);
v_setNextMacroScope_1929_ = lean_ctor_get(v_inst_1927_, 2);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_inst_1927_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_inst_1927_, 0);
lean_dec(v_unused_1939_);
v___x_1931_ = v_inst_1927_;
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_setNextMacroScope_1929_);
lean_inc(v_getNextMacroScope_1928_);
lean_dec(v_inst_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___f_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
lean_inc(v_inst_1925_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1933_, 0, v_setNextMacroScope_1929_);
lean_closure_set(v___f_1933_, 1, v_inst_1925_);
v___x_1934_ = lean_apply_2(v_inst_1925_, lean_box(0), v_getNextMacroScope_1928_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 2, v___f_1933_);
lean_ctor_set(v___x_1931_, 1, v___x_1934_);
lean_ctor_set(v___x_1931_, 0, v_inst_1926_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_inst_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v___f_1933_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1940_, lean_object* v_n_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v_getNextMacroScope_1945_; lean_object* v_setNextMacroScope_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1955_; 
v_getNextMacroScope_1945_ = lean_ctor_get(v_inst_1944_, 1);
v_setNextMacroScope_1946_ = lean_ctor_get(v_inst_1944_, 2);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_inst_1944_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v_inst_1944_, 0);
lean_dec(v_unused_1956_);
v___x_1948_ = v_inst_1944_;
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_setNextMacroScope_1946_);
lean_inc(v_getNextMacroScope_1945_);
lean_dec(v_inst_1944_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
lean_inc(v_inst_1942_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1950_, 0, v_setNextMacroScope_1946_);
lean_closure_set(v___f_1950_, 1, v_inst_1942_);
v___x_1951_ = lean_apply_2(v_inst_1942_, lean_box(0), v_getNextMacroScope_1945_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 2, v___f_1950_);
lean_ctor_set(v___x_1948_, 1, v___x_1951_);
lean_ctor_set(v___x_1948_, 0, v_inst_1943_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_inst_1943_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v___f_1950_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1957_, lean_object* v_snd_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_toMonadRef_1961_, lean_object* v_inst_1962_, lean_object* v_fst_1963_, uint8_t v_____do__lift_1964_){
_start:
{
if (v_____do__lift_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec(v_fst_1963_);
lean_dec(v_inst_1962_);
lean_dec_ref(v_toMonadRef_1961_);
lean_dec_ref(v_inst_1960_);
lean_dec_ref(v_inst_1959_);
lean_dec_ref(v_snd_1958_);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_apply_2(v_toPure_1957_, lean_box(0), v___x_1965_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v_toPure_1957_);
v___x_1967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_snd_1958_);
v___x_1968_ = l_Lean_MessageData_ofFormat(v___x_1967_);
v___x_1969_ = l_Lean_addTrace___redArg(v_inst_1959_, v_inst_1960_, v_toMonadRef_1961_, v_inst_1962_, v_fst_1963_, v___x_1968_);
return v___x_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1970_, lean_object* v_snd_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_toMonadRef_1974_, lean_object* v_inst_1975_, lean_object* v_fst_1976_, lean_object* v_____do__lift_1977_){
_start:
{
uint8_t v_____do__lift_1350__boxed_1978_; lean_object* v_res_1979_; 
v_____do__lift_1350__boxed_1978_ = lean_unbox(v_____do__lift_1977_);
v_res_1979_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1970_, v_snd_1971_, v_inst_1972_, v_inst_1973_, v_toMonadRef_1974_, v_inst_1975_, v_fst_1976_, v_____do__lift_1350__boxed_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_toMonadRef_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_toBind_1986_, lean_object* v_x_1987_){
_start:
{
lean_object* v_fst_1988_; lean_object* v_snd_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_fst_1988_ = lean_ctor_get(v_x_1987_, 0);
lean_inc(v_fst_1988_);
v_snd_1989_ = lean_ctor_get(v_x_1987_, 1);
lean_inc(v_snd_1989_);
lean_dec_ref(v_x_1987_);
lean_inc(v_fst_1988_);
lean_inc_ref(v_inst_1982_);
lean_inc_ref(v_inst_1981_);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1990_, 0, v_toPure_1980_);
lean_closure_set(v___f_1990_, 1, v_snd_1989_);
lean_closure_set(v___f_1990_, 2, v_inst_1981_);
lean_closure_set(v___f_1990_, 3, v_inst_1982_);
lean_closure_set(v___f_1990_, 4, v_toMonadRef_1983_);
lean_closure_set(v___f_1990_, 5, v_inst_1984_);
lean_closure_set(v___f_1990_, 6, v_fst_1988_);
v___x_1991_ = l_Lean_isTracingEnabledFor___redArg(v_inst_1981_, v_inst_1982_, v_inst_1985_, v_fst_1988_);
v___x_1992_ = lean_apply_4(v_toBind_1986_, lean_box(0), lean_box(0), v___x_1991_, v___f_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_env_1993_, lean_object* v___x_1994_, lean_object* v___x_1995_, lean_object* v_stx_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1993_, v_stx_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v___y_1997_);
lean_dec(v___x_1995_);
lean_dec_ref(v___x_1994_);
v_a_2001_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_1999_, 0);
lean_dec(v_unused_2010_);
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_2001_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2041_; 
v_val_2011_ = lean_ctor_get(v_a_2000_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2013_ = v_a_2000_;
v_isShared_2014_ = v_isSharedCheck_2041_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_val_2011_);
lean_dec(v_a_2000_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2041_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_snd_2015_; 
v_snd_2015_ = lean_ctor_get(v_val_2011_, 1);
lean_inc(v_snd_2015_);
lean_dec(v_val_2011_);
if (lean_obj_tag(v_snd_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_2013_);
v_a_2016_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_1999_);
v_a_2017_ = lean_ctor_get(v_snd_2015_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_snd_2015_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2019_ = v_snd_2015_;
v_isShared_2020_ = v_isSharedCheck_2026_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v_snd_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2026_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_1129__overap_2023_; lean_object* v___x_2024_; 
v___x_1129__overap_2023_ = l_liftExcept___redArg(v___x_1994_, v___x_1995_, v___x_2022_);
v___x_2024_ = lean_apply_2(v___x_1129__overap_2023_, v___y_1997_, v_a_2016_);
return v___x_2024_;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2040_; 
v_a_2027_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_1999_);
v_a_2028_ = lean_ctor_get(v_snd_2015_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_snd_2015_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2030_ = v_snd_2015_;
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v_snd_2015_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v_a_2028_);
v___x_2033_ = v___x_2013_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_1133__overap_2036_; lean_object* v___x_2037_; 
v___x_1133__overap_2036_ = l_liftExcept___redArg(v___x_1994_, v___x_1995_, v___x_2035_);
v___x_2037_ = lean_apply_2(v___x_1133__overap_2036_, v___y_1997_, v_a_2027_);
return v___x_2037_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___y_1997_);
lean_dec(v___x_1995_);
lean_dec_ref(v___x_1994_);
v_a_2042_ = lean_ctor_get(v___x_1999_, 0);
v_a_2043_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1999_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_inc(v_a_2042_);
lean_dec(v___x_1999_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_env_2051_, lean_object* v_declName_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v___x_2055_; lean_object* v_env_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2055_ = 0;
v_env_2056_ = l_Lean_Environment_setExporting(v_env_2051_, v___x_2055_);
lean_inc(v_declName_2052_);
v___x_2057_ = l_Lean_mkPrivateName(v_env_2056_, v_declName_2052_);
v___x_2058_ = 1;
lean_inc_ref(v_env_2056_);
v___x_2059_ = l_Lean_Environment_contains(v_env_2056_, v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = l_Lean_privateToUserName(v_declName_2052_);
v___x_2061_ = l_Lean_Environment_contains(v_env_2056_, v___x_2060_, v___x_2058_);
v___x_2062_ = lean_box(v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___y_2054_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v_env_2056_);
lean_dec(v_declName_2052_);
v___x_2064_ = lean_box(v___x_2059_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___y_2054_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3___boxed(lean_object* v_env_2066_, lean_object* v_declName_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Elab_liftMacroM___redArg___lam__3(v_env_2066_, v_declName_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_2071_, lean_object* v_currNamespace_2072_, lean_object* v_openDecls_2073_, lean_object* v_n_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = l_Lean_ResolveName_resolveNamespace(v_env_2071_, v_currNamespace_2072_, v_openDecls_2073_, v_n_2074_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2079_, lean_object* v_currNamespace_2080_, lean_object* v_openDecls_2081_, lean_object* v_n_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2079_, v_currNamespace_2080_, v_openDecls_2081_, v_n_2082_, v___y_2083_, v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2086_, lean_object* v_opts_2087_, lean_object* v_currNamespace_2088_, lean_object* v_openDecls_2089_, lean_object* v_n_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = l_Lean_ResolveName_resolveGlobalName(v_env_2086_, v_opts_2087_, v_currNamespace_2088_, v_openDecls_2089_, v_n_2090_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2095_, lean_object* v_opts_2096_, lean_object* v_currNamespace_2097_, lean_object* v_openDecls_2098_, lean_object* v_n_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2095_, v_opts_2096_, v_currNamespace_2097_, v_openDecls_2098_, v_n_2099_, v___y_2100_, v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec_ref(v_opts_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_toPure_2103_, lean_object* v_a_2104_, lean_object* v_____r_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_apply_2(v_toPure_2103_, lean_box(0), v_a_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_traceMsgs_2107_, lean_object* v_inst_2108_, lean_object* v___f_2109_, lean_object* v_toBind_2110_, lean_object* v___f_2111_, lean_object* v_____r_2112_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = l_List_reverse___redArg(v_traceMsgs_2107_);
v___x_2114_ = l_List_forM___redArg(v_inst_2108_, v___x_2113_, v___f_2109_);
v___x_2115_ = lean_apply_4(v_toBind_2110_, lean_box(0), lean_box(0), v___x_2114_, v___f_2111_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_setNextMacroScope_2116_, lean_object* v_macroScope_2117_, lean_object* v_toBind_2118_, lean_object* v___f_2119_, lean_object* v_____s_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_apply_1(v_setNextMacroScope_2116_, v_macroScope_2117_);
v___x_2122_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v___x_2121_, v___f_2119_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v___x_2123_, lean_object* v_toPure_2124_, lean_object* v_____r_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2123_);
v___x_2127_ = lean_apply_2(v_toPure_2124_, lean_box(0), v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_toMonadRef_2132_, lean_object* v_inst_2133_, lean_object* v_toBind_2134_, lean_object* v___f_2135_, lean_object* v_a_2136_, lean_object* v_x_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = 1;
v___x_2140_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2128_, v_inst_2129_, v_inst_2130_, v_inst_2131_, v_toMonadRef_2132_, v_inst_2133_, v_a_2136_, v___x_2139_);
v___x_2141_ = lean_apply_4(v_toBind_2134_, lean_box(0), lean_box(0), v___x_2140_, v___f_2135_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v_methods_2143_, lean_object* v_____do__lift_2144_, lean_object* v_____do__lift_2145_, lean_object* v_____do__lift_2146_, lean_object* v_____do__lift_2147_, lean_object* v_____do__lift_2148_, lean_object* v_x_2149_, lean_object* v_toPure_2150_, lean_object* v_inst_2151_, lean_object* v___f_2152_, lean_object* v_toBind_2153_, lean_object* v_setNextMacroScope_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_toMonadRef_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_toMonadExceptOf_2161_, lean_object* v_____do__lift_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2163_, 0, v_methods_2143_);
lean_ctor_set(v___x_2163_, 1, v_____do__lift_2144_);
lean_ctor_set(v___x_2163_, 2, v_____do__lift_2145_);
lean_ctor_set(v___x_2163_, 3, v_____do__lift_2146_);
lean_ctor_set(v___x_2163_, 4, v_____do__lift_2147_);
lean_ctor_set(v___x_2163_, 5, v_____do__lift_2148_);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2165_, 0, v_____do__lift_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_ctor_set(v___x_2165_, 2, v___x_2164_);
v___x_2166_ = lean_apply_2(v_x_2149_, v___x_2163_, v___x_2165_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v_a_2168_; lean_object* v_macroScope_2169_; lean_object* v_traceMsgs_2170_; lean_object* v_expandedMacroDecls_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___f_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v_toMonadExceptOf_2161_);
lean_dec_ref(v_inst_2160_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_a_2167_);
v_a_2168_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2166_);
v_macroScope_2169_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_macroScope_2169_);
v_traceMsgs_2170_ = lean_ctor_get(v_a_2167_, 1);
lean_inc(v_traceMsgs_2170_);
v_expandedMacroDecls_2171_ = lean_ctor_get(v_a_2167_, 2);
lean_inc(v_expandedMacroDecls_2171_);
lean_dec(v_a_2167_);
lean_inc(v_toPure_2150_);
v___f_2172_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6), 3, 2);
lean_closure_set(v___f_2172_, 0, v_toPure_2150_);
lean_closure_set(v___f_2172_, 1, v_a_2168_);
lean_inc(v_toBind_2153_);
lean_inc_ref(v_inst_2151_);
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7), 6, 5);
lean_closure_set(v___f_2173_, 0, v_traceMsgs_2170_);
lean_closure_set(v___f_2173_, 1, v_inst_2151_);
lean_closure_set(v___f_2173_, 2, v___f_2152_);
lean_closure_set(v___f_2173_, 3, v_toBind_2153_);
lean_closure_set(v___f_2173_, 4, v___f_2172_);
lean_inc(v_toBind_2153_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2174_, 0, v_setNextMacroScope_2154_);
lean_closure_set(v___f_2174_, 1, v_macroScope_2169_);
lean_closure_set(v___f_2174_, 2, v_toBind_2153_);
lean_closure_set(v___f_2174_, 3, v___f_2173_);
v___x_2175_ = lean_box(0);
v___f_2176_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 3, 2);
lean_closure_set(v___f_2176_, 0, v___x_2175_);
lean_closure_set(v___f_2176_, 1, v_toPure_2150_);
lean_inc(v_toBind_2153_);
lean_inc_ref(v_inst_2151_);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 11, 8);
lean_closure_set(v___f_2177_, 0, v_inst_2151_);
lean_closure_set(v___f_2177_, 1, v_inst_2155_);
lean_closure_set(v___f_2177_, 2, v_inst_2156_);
lean_closure_set(v___f_2177_, 3, v_inst_2157_);
lean_closure_set(v___f_2177_, 4, v_toMonadRef_2158_);
lean_closure_set(v___f_2177_, 5, v_inst_2159_);
lean_closure_set(v___f_2177_, 6, v_toBind_2153_);
lean_closure_set(v___f_2177_, 7, v___f_2176_);
v___x_2178_ = l_List_forIn_x27_loop___redArg(v_inst_2151_, v___f_2177_, v_expandedMacroDecls_2171_, v___x_2175_);
v___x_2179_ = lean_apply_4(v_toBind_2153_, lean_box(0), lean_box(0), v___x_2178_, v___f_2174_);
return v___x_2179_;
}
else
{
lean_object* v_a_2180_; 
lean_dec(v_inst_2159_);
lean_dec_ref(v_toMonadRef_2158_);
lean_dec(v_inst_2157_);
lean_dec_ref(v_inst_2156_);
lean_dec_ref(v_inst_2155_);
lean_dec(v_setNextMacroScope_2154_);
lean_dec(v_toBind_2153_);
lean_dec(v___f_2152_);
lean_dec(v_toPure_2150_);
v_a_2180_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2166_);
if (lean_obj_tag(v_a_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
lean_dec_ref(v_toMonadExceptOf_2161_);
v_a_2181_ = lean_ctor_get(v_a_2180_, 0);
lean_inc(v_a_2181_);
v_a_2182_ = lean_ctor_get(v_a_2180_, 1);
lean_inc_ref(v_a_2182_);
lean_dec_ref(v_a_2180_);
v___x_2183_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__11___closed__0));
v___x_2184_ = lean_string_dec_eq(v_a_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2182_);
v___x_2186_ = l_Lean_MessageData_ofFormat(v___x_2185_);
v___x_2187_ = l_Lean_throwErrorAt___redArg(v_inst_2151_, v_inst_2160_, v_a_2181_, v___x_2186_);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v_a_2182_);
lean_dec_ref(v_inst_2151_);
v___x_2188_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2160_, v_a_2181_);
return v___x_2188_;
}
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_inst_2160_);
lean_dec_ref(v_inst_2151_);
v___x_2189_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2161_);
return v___x_2189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_methods_2190_ = _args[0];
lean_object* v_____do__lift_2191_ = _args[1];
lean_object* v_____do__lift_2192_ = _args[2];
lean_object* v_____do__lift_2193_ = _args[3];
lean_object* v_____do__lift_2194_ = _args[4];
lean_object* v_____do__lift_2195_ = _args[5];
lean_object* v_x_2196_ = _args[6];
lean_object* v_toPure_2197_ = _args[7];
lean_object* v_inst_2198_ = _args[8];
lean_object* v___f_2199_ = _args[9];
lean_object* v_toBind_2200_ = _args[10];
lean_object* v_setNextMacroScope_2201_ = _args[11];
lean_object* v_inst_2202_ = _args[12];
lean_object* v_inst_2203_ = _args[13];
lean_object* v_inst_2204_ = _args[14];
lean_object* v_toMonadRef_2205_ = _args[15];
lean_object* v_inst_2206_ = _args[16];
lean_object* v_inst_2207_ = _args[17];
lean_object* v_toMonadExceptOf_2208_ = _args[18];
lean_object* v_____do__lift_2209_ = _args[19];
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Elab_liftMacroM___redArg___lam__11(v_methods_2190_, v_____do__lift_2191_, v_____do__lift_2192_, v_____do__lift_2193_, v_____do__lift_2194_, v_____do__lift_2195_, v_x_2196_, v_toPure_2197_, v_inst_2198_, v___f_2199_, v_toBind_2200_, v_setNextMacroScope_2201_, v_inst_2202_, v_inst_2203_, v_inst_2204_, v_toMonadRef_2205_, v_inst_2206_, v_inst_2207_, v_toMonadExceptOf_2208_, v_____do__lift_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_methods_2211_, lean_object* v_____do__lift_2212_, lean_object* v_____do__lift_2213_, lean_object* v_____do__lift_2214_, lean_object* v_____do__lift_2215_, lean_object* v_x_2216_, lean_object* v_toPure_2217_, lean_object* v_inst_2218_, lean_object* v___f_2219_, lean_object* v_toBind_2220_, lean_object* v_setNextMacroScope_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_toMonadRef_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_toMonadExceptOf_2228_, lean_object* v_getNextMacroScope_2229_, lean_object* v_____do__lift_2230_){
_start:
{
lean_object* v___f_2231_; lean_object* v___x_2232_; 
lean_inc(v_toBind_2220_);
v___f_2231_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11___boxed), 20, 19);
lean_closure_set(v___f_2231_, 0, v_methods_2211_);
lean_closure_set(v___f_2231_, 1, v_____do__lift_2212_);
lean_closure_set(v___f_2231_, 2, v_____do__lift_2213_);
lean_closure_set(v___f_2231_, 3, v_____do__lift_2214_);
lean_closure_set(v___f_2231_, 4, v_____do__lift_2230_);
lean_closure_set(v___f_2231_, 5, v_____do__lift_2215_);
lean_closure_set(v___f_2231_, 6, v_x_2216_);
lean_closure_set(v___f_2231_, 7, v_toPure_2217_);
lean_closure_set(v___f_2231_, 8, v_inst_2218_);
lean_closure_set(v___f_2231_, 9, v___f_2219_);
lean_closure_set(v___f_2231_, 10, v_toBind_2220_);
lean_closure_set(v___f_2231_, 11, v_setNextMacroScope_2221_);
lean_closure_set(v___f_2231_, 12, v_inst_2222_);
lean_closure_set(v___f_2231_, 13, v_inst_2223_);
lean_closure_set(v___f_2231_, 14, v_inst_2224_);
lean_closure_set(v___f_2231_, 15, v_toMonadRef_2225_);
lean_closure_set(v___f_2231_, 16, v_inst_2226_);
lean_closure_set(v___f_2231_, 17, v_inst_2227_);
lean_closure_set(v___f_2231_, 18, v_toMonadExceptOf_2228_);
v___x_2232_ = lean_apply_4(v_toBind_2220_, lean_box(0), lean_box(0), v_getNextMacroScope_2229_, v___f_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_methods_2233_ = _args[0];
lean_object* v_____do__lift_2234_ = _args[1];
lean_object* v_____do__lift_2235_ = _args[2];
lean_object* v_____do__lift_2236_ = _args[3];
lean_object* v_____do__lift_2237_ = _args[4];
lean_object* v_x_2238_ = _args[5];
lean_object* v_toPure_2239_ = _args[6];
lean_object* v_inst_2240_ = _args[7];
lean_object* v___f_2241_ = _args[8];
lean_object* v_toBind_2242_ = _args[9];
lean_object* v_setNextMacroScope_2243_ = _args[10];
lean_object* v_inst_2244_ = _args[11];
lean_object* v_inst_2245_ = _args[12];
lean_object* v_inst_2246_ = _args[13];
lean_object* v_toMonadRef_2247_ = _args[14];
lean_object* v_inst_2248_ = _args[15];
lean_object* v_inst_2249_ = _args[16];
lean_object* v_toMonadExceptOf_2250_ = _args[17];
lean_object* v_getNextMacroScope_2251_ = _args[18];
lean_object* v_____do__lift_2252_ = _args[19];
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Elab_liftMacroM___redArg___lam__12(v_methods_2233_, v_____do__lift_2234_, v_____do__lift_2235_, v_____do__lift_2236_, v_____do__lift_2237_, v_x_2238_, v_toPure_2239_, v_inst_2240_, v___f_2241_, v_toBind_2242_, v_setNextMacroScope_2243_, v_inst_2244_, v_inst_2245_, v_inst_2246_, v_toMonadRef_2247_, v_inst_2248_, v_inst_2249_, v_toMonadExceptOf_2250_, v_getNextMacroScope_2251_, v_____do__lift_2252_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2254_, lean_object* v_____do__lift_2255_, lean_object* v_____do__lift_2256_, lean_object* v_____do__lift_2257_, lean_object* v_x_2258_, lean_object* v_toPure_2259_, lean_object* v_inst_2260_, lean_object* v___f_2261_, lean_object* v_toBind_2262_, lean_object* v_setNextMacroScope_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_toMonadRef_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_toMonadExceptOf_2270_, lean_object* v_getNextMacroScope_2271_, lean_object* v_getMaxRecDepth_2272_, lean_object* v_____do__lift_2273_){
_start:
{
lean_object* v___f_2274_; lean_object* v___x_2275_; 
lean_inc(v_toBind_2262_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12___boxed), 20, 19);
lean_closure_set(v___f_2274_, 0, v_methods_2254_);
lean_closure_set(v___f_2274_, 1, v_____do__lift_2255_);
lean_closure_set(v___f_2274_, 2, v_____do__lift_2256_);
lean_closure_set(v___f_2274_, 3, v_____do__lift_2273_);
lean_closure_set(v___f_2274_, 4, v_____do__lift_2257_);
lean_closure_set(v___f_2274_, 5, v_x_2258_);
lean_closure_set(v___f_2274_, 6, v_toPure_2259_);
lean_closure_set(v___f_2274_, 7, v_inst_2260_);
lean_closure_set(v___f_2274_, 8, v___f_2261_);
lean_closure_set(v___f_2274_, 9, v_toBind_2262_);
lean_closure_set(v___f_2274_, 10, v_setNextMacroScope_2263_);
lean_closure_set(v___f_2274_, 11, v_inst_2264_);
lean_closure_set(v___f_2274_, 12, v_inst_2265_);
lean_closure_set(v___f_2274_, 13, v_inst_2266_);
lean_closure_set(v___f_2274_, 14, v_toMonadRef_2267_);
lean_closure_set(v___f_2274_, 15, v_inst_2268_);
lean_closure_set(v___f_2274_, 16, v_inst_2269_);
lean_closure_set(v___f_2274_, 17, v_toMonadExceptOf_2270_);
lean_closure_set(v___f_2274_, 18, v_getNextMacroScope_2271_);
v___x_2275_ = lean_apply_4(v_toBind_2262_, lean_box(0), lean_box(0), v_getMaxRecDepth_2272_, v___f_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2276_ = _args[0];
lean_object* v_____do__lift_2277_ = _args[1];
lean_object* v_____do__lift_2278_ = _args[2];
lean_object* v_____do__lift_2279_ = _args[3];
lean_object* v_x_2280_ = _args[4];
lean_object* v_toPure_2281_ = _args[5];
lean_object* v_inst_2282_ = _args[6];
lean_object* v___f_2283_ = _args[7];
lean_object* v_toBind_2284_ = _args[8];
lean_object* v_setNextMacroScope_2285_ = _args[9];
lean_object* v_inst_2286_ = _args[10];
lean_object* v_inst_2287_ = _args[11];
lean_object* v_inst_2288_ = _args[12];
lean_object* v_toMonadRef_2289_ = _args[13];
lean_object* v_inst_2290_ = _args[14];
lean_object* v_inst_2291_ = _args[15];
lean_object* v_toMonadExceptOf_2292_ = _args[16];
lean_object* v_getNextMacroScope_2293_ = _args[17];
lean_object* v_getMaxRecDepth_2294_ = _args[18];
lean_object* v_____do__lift_2295_ = _args[19];
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2276_, v_____do__lift_2277_, v_____do__lift_2278_, v_____do__lift_2279_, v_x_2280_, v_toPure_2281_, v_inst_2282_, v___f_2283_, v_toBind_2284_, v_setNextMacroScope_2285_, v_inst_2286_, v_inst_2287_, v_inst_2288_, v_toMonadRef_2289_, v_inst_2290_, v_inst_2291_, v_toMonadExceptOf_2292_, v_getNextMacroScope_2293_, v_getMaxRecDepth_2294_, v_____do__lift_2295_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_inst_2297_, lean_object* v_methods_2298_, lean_object* v_____do__lift_2299_, lean_object* v_____do__lift_2300_, lean_object* v_x_2301_, lean_object* v_toPure_2302_, lean_object* v_inst_2303_, lean_object* v___f_2304_, lean_object* v_toBind_2305_, lean_object* v_setNextMacroScope_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_toMonadRef_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_toMonadExceptOf_2313_, lean_object* v_getNextMacroScope_2314_, lean_object* v_____do__lift_2315_){
_start:
{
lean_object* v_getRecDepth_2316_; lean_object* v_getMaxRecDepth_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; 
v_getRecDepth_2316_ = lean_ctor_get(v_inst_2297_, 1);
lean_inc(v_getRecDepth_2316_);
v_getMaxRecDepth_2317_ = lean_ctor_get(v_inst_2297_, 2);
lean_inc(v_getMaxRecDepth_2317_);
lean_dec_ref(v_inst_2297_);
lean_inc(v_toBind_2305_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2318_, 0, v_methods_2298_);
lean_closure_set(v___f_2318_, 1, v_____do__lift_2315_);
lean_closure_set(v___f_2318_, 2, v_____do__lift_2299_);
lean_closure_set(v___f_2318_, 3, v_____do__lift_2300_);
lean_closure_set(v___f_2318_, 4, v_x_2301_);
lean_closure_set(v___f_2318_, 5, v_toPure_2302_);
lean_closure_set(v___f_2318_, 6, v_inst_2303_);
lean_closure_set(v___f_2318_, 7, v___f_2304_);
lean_closure_set(v___f_2318_, 8, v_toBind_2305_);
lean_closure_set(v___f_2318_, 9, v_setNextMacroScope_2306_);
lean_closure_set(v___f_2318_, 10, v_inst_2307_);
lean_closure_set(v___f_2318_, 11, v_inst_2308_);
lean_closure_set(v___f_2318_, 12, v_inst_2309_);
lean_closure_set(v___f_2318_, 13, v_toMonadRef_2310_);
lean_closure_set(v___f_2318_, 14, v_inst_2311_);
lean_closure_set(v___f_2318_, 15, v_inst_2312_);
lean_closure_set(v___f_2318_, 16, v_toMonadExceptOf_2313_);
lean_closure_set(v___f_2318_, 17, v_getNextMacroScope_2314_);
lean_closure_set(v___f_2318_, 18, v_getMaxRecDepth_2317_);
v___x_2319_ = lean_apply_4(v_toBind_2305_, lean_box(0), lean_box(0), v_getRecDepth_2316_, v___f_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_inst_2320_ = _args[0];
lean_object* v_methods_2321_ = _args[1];
lean_object* v_____do__lift_2322_ = _args[2];
lean_object* v_____do__lift_2323_ = _args[3];
lean_object* v_x_2324_ = _args[4];
lean_object* v_toPure_2325_ = _args[5];
lean_object* v_inst_2326_ = _args[6];
lean_object* v___f_2327_ = _args[7];
lean_object* v_toBind_2328_ = _args[8];
lean_object* v_setNextMacroScope_2329_ = _args[9];
lean_object* v_inst_2330_ = _args[10];
lean_object* v_inst_2331_ = _args[11];
lean_object* v_inst_2332_ = _args[12];
lean_object* v_toMonadRef_2333_ = _args[13];
lean_object* v_inst_2334_ = _args[14];
lean_object* v_inst_2335_ = _args[15];
lean_object* v_toMonadExceptOf_2336_ = _args[16];
lean_object* v_getNextMacroScope_2337_ = _args[17];
lean_object* v_____do__lift_2338_ = _args[18];
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_inst_2320_, v_methods_2321_, v_____do__lift_2322_, v_____do__lift_2323_, v_x_2324_, v_toPure_2325_, v_inst_2326_, v___f_2327_, v_toBind_2328_, v_setNextMacroScope_2329_, v_inst_2330_, v_inst_2331_, v_inst_2332_, v_toMonadRef_2333_, v_inst_2334_, v_inst_2335_, v_toMonadExceptOf_2336_, v_getNextMacroScope_2337_, v_____do__lift_2338_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_inst_2340_, lean_object* v_methods_2341_, lean_object* v_____do__lift_2342_, lean_object* v_x_2343_, lean_object* v_toPure_2344_, lean_object* v_inst_2345_, lean_object* v___f_2346_, lean_object* v_toBind_2347_, lean_object* v_setNextMacroScope_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_toMonadRef_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_toMonadExceptOf_2355_, lean_object* v_getNextMacroScope_2356_, lean_object* v_getContext_2357_, lean_object* v_____do__lift_2358_){
_start:
{
lean_object* v___f_2359_; lean_object* v___x_2360_; 
lean_inc(v_toBind_2347_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 19, 18);
lean_closure_set(v___f_2359_, 0, v_inst_2340_);
lean_closure_set(v___f_2359_, 1, v_methods_2341_);
lean_closure_set(v___f_2359_, 2, v_____do__lift_2358_);
lean_closure_set(v___f_2359_, 3, v_____do__lift_2342_);
lean_closure_set(v___f_2359_, 4, v_x_2343_);
lean_closure_set(v___f_2359_, 5, v_toPure_2344_);
lean_closure_set(v___f_2359_, 6, v_inst_2345_);
lean_closure_set(v___f_2359_, 7, v___f_2346_);
lean_closure_set(v___f_2359_, 8, v_toBind_2347_);
lean_closure_set(v___f_2359_, 9, v_setNextMacroScope_2348_);
lean_closure_set(v___f_2359_, 10, v_inst_2349_);
lean_closure_set(v___f_2359_, 11, v_inst_2350_);
lean_closure_set(v___f_2359_, 12, v_inst_2351_);
lean_closure_set(v___f_2359_, 13, v_toMonadRef_2352_);
lean_closure_set(v___f_2359_, 14, v_inst_2353_);
lean_closure_set(v___f_2359_, 15, v_inst_2354_);
lean_closure_set(v___f_2359_, 16, v_toMonadExceptOf_2355_);
lean_closure_set(v___f_2359_, 17, v_getNextMacroScope_2356_);
v___x_2360_ = lean_apply_4(v_toBind_2347_, lean_box(0), lean_box(0), v_getContext_2357_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_inst_2361_ = _args[0];
lean_object* v_methods_2362_ = _args[1];
lean_object* v_____do__lift_2363_ = _args[2];
lean_object* v_x_2364_ = _args[3];
lean_object* v_toPure_2365_ = _args[4];
lean_object* v_inst_2366_ = _args[5];
lean_object* v___f_2367_ = _args[6];
lean_object* v_toBind_2368_ = _args[7];
lean_object* v_setNextMacroScope_2369_ = _args[8];
lean_object* v_inst_2370_ = _args[9];
lean_object* v_inst_2371_ = _args[10];
lean_object* v_inst_2372_ = _args[11];
lean_object* v_toMonadRef_2373_ = _args[12];
lean_object* v_inst_2374_ = _args[13];
lean_object* v_inst_2375_ = _args[14];
lean_object* v_toMonadExceptOf_2376_ = _args[15];
lean_object* v_getNextMacroScope_2377_ = _args[16];
lean_object* v_getContext_2378_ = _args[17];
lean_object* v_____do__lift_2379_ = _args[18];
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_inst_2361_, v_methods_2362_, v_____do__lift_2363_, v_x_2364_, v_toPure_2365_, v_inst_2366_, v___f_2367_, v_toBind_2368_, v_setNextMacroScope_2369_, v_inst_2370_, v_inst_2371_, v_inst_2372_, v_toMonadRef_2373_, v_inst_2374_, v_inst_2375_, v_toMonadExceptOf_2376_, v_getNextMacroScope_2377_, v_getContext_2378_, v_____do__lift_2379_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_toMonadQuotation_2381_, lean_object* v_inst_2382_, lean_object* v_methods_2383_, lean_object* v_x_2384_, lean_object* v_toPure_2385_, lean_object* v_inst_2386_, lean_object* v___f_2387_, lean_object* v_toBind_2388_, lean_object* v_setNextMacroScope_2389_, lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_toMonadRef_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_toMonadExceptOf_2396_, lean_object* v_getNextMacroScope_2397_, lean_object* v_____do__lift_2398_){
_start:
{
lean_object* v_getCurrMacroScope_2399_; lean_object* v_getContext_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; 
v_getCurrMacroScope_2399_ = lean_ctor_get(v_toMonadQuotation_2381_, 1);
lean_inc(v_getCurrMacroScope_2399_);
v_getContext_2400_ = lean_ctor_get(v_toMonadQuotation_2381_, 2);
lean_inc(v_getContext_2400_);
lean_dec_ref(v_toMonadQuotation_2381_);
lean_inc(v_toBind_2388_);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 19, 18);
lean_closure_set(v___f_2401_, 0, v_inst_2382_);
lean_closure_set(v___f_2401_, 1, v_methods_2383_);
lean_closure_set(v___f_2401_, 2, v_____do__lift_2398_);
lean_closure_set(v___f_2401_, 3, v_x_2384_);
lean_closure_set(v___f_2401_, 4, v_toPure_2385_);
lean_closure_set(v___f_2401_, 5, v_inst_2386_);
lean_closure_set(v___f_2401_, 6, v___f_2387_);
lean_closure_set(v___f_2401_, 7, v_toBind_2388_);
lean_closure_set(v___f_2401_, 8, v_setNextMacroScope_2389_);
lean_closure_set(v___f_2401_, 9, v_inst_2390_);
lean_closure_set(v___f_2401_, 10, v_inst_2391_);
lean_closure_set(v___f_2401_, 11, v_inst_2392_);
lean_closure_set(v___f_2401_, 12, v_toMonadRef_2393_);
lean_closure_set(v___f_2401_, 13, v_inst_2394_);
lean_closure_set(v___f_2401_, 14, v_inst_2395_);
lean_closure_set(v___f_2401_, 15, v_toMonadExceptOf_2396_);
lean_closure_set(v___f_2401_, 16, v_getNextMacroScope_2397_);
lean_closure_set(v___f_2401_, 17, v_getContext_2400_);
v___x_2402_ = lean_apply_4(v_toBind_2388_, lean_box(0), lean_box(0), v_getCurrMacroScope_2399_, v___f_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2403_ = _args[0];
lean_object* v_inst_2404_ = _args[1];
lean_object* v_methods_2405_ = _args[2];
lean_object* v_x_2406_ = _args[3];
lean_object* v_toPure_2407_ = _args[4];
lean_object* v_inst_2408_ = _args[5];
lean_object* v___f_2409_ = _args[6];
lean_object* v_toBind_2410_ = _args[7];
lean_object* v_setNextMacroScope_2411_ = _args[8];
lean_object* v_inst_2412_ = _args[9];
lean_object* v_inst_2413_ = _args[10];
lean_object* v_inst_2414_ = _args[11];
lean_object* v_toMonadRef_2415_ = _args[12];
lean_object* v_inst_2416_ = _args[13];
lean_object* v_inst_2417_ = _args[14];
lean_object* v_toMonadExceptOf_2418_ = _args[15];
lean_object* v_getNextMacroScope_2419_ = _args[16];
lean_object* v_____do__lift_2420_ = _args[17];
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_toMonadQuotation_2403_, v_inst_2404_, v_methods_2405_, v_x_2406_, v_toPure_2407_, v_inst_2408_, v___f_2409_, v_toBind_2410_, v_setNextMacroScope_2411_, v_inst_2412_, v_inst_2413_, v_inst_2414_, v_toMonadRef_2415_, v_inst_2416_, v_inst_2417_, v_toMonadExceptOf_2418_, v_getNextMacroScope_2419_, v_____do__lift_2420_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_toMonadRef_2422_, lean_object* v_env_2423_, lean_object* v_currNamespace_2424_, lean_object* v_opts_2425_, lean_object* v___x_2426_, lean_object* v___f_2427_, lean_object* v___f_2428_, lean_object* v_toMonadQuotation_2429_, lean_object* v_inst_2430_, lean_object* v_x_2431_, lean_object* v_toPure_2432_, lean_object* v_inst_2433_, lean_object* v___f_2434_, lean_object* v_toBind_2435_, lean_object* v_setNextMacroScope_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_toMonadExceptOf_2442_, lean_object* v_getNextMacroScope_2443_, lean_object* v_openDecls_2444_){
_start:
{
lean_object* v_getRef_2445_; lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; lean_object* v_methods_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v_getRef_2445_ = lean_ctor_get(v_toMonadRef_2422_, 0);
lean_inc(v_getRef_2445_);
lean_inc(v_openDecls_2444_);
lean_inc(v_currNamespace_2424_);
lean_inc_ref(v_env_2423_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2446_, 0, v_env_2423_);
lean_closure_set(v___f_2446_, 1, v_currNamespace_2424_);
lean_closure_set(v___f_2446_, 2, v_openDecls_2444_);
lean_inc(v_currNamespace_2424_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 7, 4);
lean_closure_set(v___f_2447_, 0, v_env_2423_);
lean_closure_set(v___f_2447_, 1, v_opts_2425_);
lean_closure_set(v___f_2447_, 2, v_currNamespace_2424_);
lean_closure_set(v___f_2447_, 3, v_openDecls_2444_);
v___x_2448_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2448_, 0, lean_box(0));
lean_closure_set(v___x_2448_, 1, lean_box(0));
lean_closure_set(v___x_2448_, 2, v___x_2426_);
lean_closure_set(v___x_2448_, 3, lean_box(0));
lean_closure_set(v___x_2448_, 4, v_currNamespace_2424_);
v_methods_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2449_, 0, v___f_2427_);
lean_ctor_set(v_methods_2449_, 1, v___x_2448_);
lean_ctor_set(v_methods_2449_, 2, v___f_2428_);
lean_ctor_set(v_methods_2449_, 3, v___f_2446_);
lean_ctor_set(v_methods_2449_, 4, v___f_2447_);
lean_inc(v_toBind_2435_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 18, 17);
lean_closure_set(v___f_2450_, 0, v_toMonadQuotation_2429_);
lean_closure_set(v___f_2450_, 1, v_inst_2430_);
lean_closure_set(v___f_2450_, 2, v_methods_2449_);
lean_closure_set(v___f_2450_, 3, v_x_2431_);
lean_closure_set(v___f_2450_, 4, v_toPure_2432_);
lean_closure_set(v___f_2450_, 5, v_inst_2433_);
lean_closure_set(v___f_2450_, 6, v___f_2434_);
lean_closure_set(v___f_2450_, 7, v_toBind_2435_);
lean_closure_set(v___f_2450_, 8, v_setNextMacroScope_2436_);
lean_closure_set(v___f_2450_, 9, v_inst_2437_);
lean_closure_set(v___f_2450_, 10, v_inst_2438_);
lean_closure_set(v___f_2450_, 11, v_inst_2439_);
lean_closure_set(v___f_2450_, 12, v_toMonadRef_2422_);
lean_closure_set(v___f_2450_, 13, v_inst_2440_);
lean_closure_set(v___f_2450_, 14, v_inst_2441_);
lean_closure_set(v___f_2450_, 15, v_toMonadExceptOf_2442_);
lean_closure_set(v___f_2450_, 16, v_getNextMacroScope_2443_);
v___x_2451_ = lean_apply_4(v_toBind_2435_, lean_box(0), lean_box(0), v_getRef_2445_, v___f_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_toMonadRef_2452_ = _args[0];
lean_object* v_env_2453_ = _args[1];
lean_object* v_currNamespace_2454_ = _args[2];
lean_object* v_opts_2455_ = _args[3];
lean_object* v___x_2456_ = _args[4];
lean_object* v___f_2457_ = _args[5];
lean_object* v___f_2458_ = _args[6];
lean_object* v_toMonadQuotation_2459_ = _args[7];
lean_object* v_inst_2460_ = _args[8];
lean_object* v_x_2461_ = _args[9];
lean_object* v_toPure_2462_ = _args[10];
lean_object* v_inst_2463_ = _args[11];
lean_object* v___f_2464_ = _args[12];
lean_object* v_toBind_2465_ = _args[13];
lean_object* v_setNextMacroScope_2466_ = _args[14];
lean_object* v_inst_2467_ = _args[15];
lean_object* v_inst_2468_ = _args[16];
lean_object* v_inst_2469_ = _args[17];
lean_object* v_inst_2470_ = _args[18];
lean_object* v_inst_2471_ = _args[19];
lean_object* v_toMonadExceptOf_2472_ = _args[20];
lean_object* v_getNextMacroScope_2473_ = _args[21];
lean_object* v_openDecls_2474_ = _args[22];
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_toMonadRef_2452_, v_env_2453_, v_currNamespace_2454_, v_opts_2455_, v___x_2456_, v___f_2457_, v___f_2458_, v_toMonadQuotation_2459_, v_inst_2460_, v_x_2461_, v_toPure_2462_, v_inst_2463_, v___f_2464_, v_toBind_2465_, v_setNextMacroScope_2466_, v_inst_2467_, v_inst_2468_, v_inst_2469_, v_inst_2470_, v_inst_2471_, v_toMonadExceptOf_2472_, v_getNextMacroScope_2473_, v_openDecls_2474_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadRef_2476_, lean_object* v_env_2477_, lean_object* v_opts_2478_, lean_object* v___x_2479_, lean_object* v___f_2480_, lean_object* v___f_2481_, lean_object* v_toMonadQuotation_2482_, lean_object* v_inst_2483_, lean_object* v_x_2484_, lean_object* v_toPure_2485_, lean_object* v_inst_2486_, lean_object* v___f_2487_, lean_object* v_toBind_2488_, lean_object* v_setNextMacroScope_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_toMonadExceptOf_2495_, lean_object* v_getNextMacroScope_2496_, lean_object* v_getOpenDecls_2497_, lean_object* v_currNamespace_2498_){
_start:
{
lean_object* v___f_2499_; lean_object* v___x_2500_; 
lean_inc(v_toBind_2488_);
v___f_2499_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_2499_, 0, v_toMonadRef_2476_);
lean_closure_set(v___f_2499_, 1, v_env_2477_);
lean_closure_set(v___f_2499_, 2, v_currNamespace_2498_);
lean_closure_set(v___f_2499_, 3, v_opts_2478_);
lean_closure_set(v___f_2499_, 4, v___x_2479_);
lean_closure_set(v___f_2499_, 5, v___f_2480_);
lean_closure_set(v___f_2499_, 6, v___f_2481_);
lean_closure_set(v___f_2499_, 7, v_toMonadQuotation_2482_);
lean_closure_set(v___f_2499_, 8, v_inst_2483_);
lean_closure_set(v___f_2499_, 9, v_x_2484_);
lean_closure_set(v___f_2499_, 10, v_toPure_2485_);
lean_closure_set(v___f_2499_, 11, v_inst_2486_);
lean_closure_set(v___f_2499_, 12, v___f_2487_);
lean_closure_set(v___f_2499_, 13, v_toBind_2488_);
lean_closure_set(v___f_2499_, 14, v_setNextMacroScope_2489_);
lean_closure_set(v___f_2499_, 15, v_inst_2490_);
lean_closure_set(v___f_2499_, 16, v_inst_2491_);
lean_closure_set(v___f_2499_, 17, v_inst_2492_);
lean_closure_set(v___f_2499_, 18, v_inst_2493_);
lean_closure_set(v___f_2499_, 19, v_inst_2494_);
lean_closure_set(v___f_2499_, 20, v_toMonadExceptOf_2495_);
lean_closure_set(v___f_2499_, 21, v_getNextMacroScope_2496_);
v___x_2500_ = lean_apply_4(v_toBind_2488_, lean_box(0), lean_box(0), v_getOpenDecls_2497_, v___f_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadRef_2501_ = _args[0];
lean_object* v_env_2502_ = _args[1];
lean_object* v_opts_2503_ = _args[2];
lean_object* v___x_2504_ = _args[3];
lean_object* v___f_2505_ = _args[4];
lean_object* v___f_2506_ = _args[5];
lean_object* v_toMonadQuotation_2507_ = _args[6];
lean_object* v_inst_2508_ = _args[7];
lean_object* v_x_2509_ = _args[8];
lean_object* v_toPure_2510_ = _args[9];
lean_object* v_inst_2511_ = _args[10];
lean_object* v___f_2512_ = _args[11];
lean_object* v_toBind_2513_ = _args[12];
lean_object* v_setNextMacroScope_2514_ = _args[13];
lean_object* v_inst_2515_ = _args[14];
lean_object* v_inst_2516_ = _args[15];
lean_object* v_inst_2517_ = _args[16];
lean_object* v_inst_2518_ = _args[17];
lean_object* v_inst_2519_ = _args[18];
lean_object* v_toMonadExceptOf_2520_ = _args[19];
lean_object* v_getNextMacroScope_2521_ = _args[20];
lean_object* v_getOpenDecls_2522_ = _args[21];
lean_object* v_currNamespace_2523_ = _args[22];
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadRef_2501_, v_env_2502_, v_opts_2503_, v___x_2504_, v___f_2505_, v___f_2506_, v_toMonadQuotation_2507_, v_inst_2508_, v_x_2509_, v_toPure_2510_, v_inst_2511_, v___f_2512_, v_toBind_2513_, v_setNextMacroScope_2514_, v_inst_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_inst_2519_, v_toMonadExceptOf_2520_, v_getNextMacroScope_2521_, v_getOpenDecls_2522_, v_currNamespace_2523_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_inst_2525_, lean_object* v_toMonadRef_2526_, lean_object* v_env_2527_, lean_object* v___x_2528_, lean_object* v___f_2529_, lean_object* v___f_2530_, lean_object* v_toMonadQuotation_2531_, lean_object* v_inst_2532_, lean_object* v_x_2533_, lean_object* v_toPure_2534_, lean_object* v_inst_2535_, lean_object* v___f_2536_, lean_object* v_toBind_2537_, lean_object* v_setNextMacroScope_2538_, lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_toMonadExceptOf_2544_, lean_object* v_getNextMacroScope_2545_, lean_object* v_opts_2546_){
_start:
{
lean_object* v_getCurrNamespace_2547_; lean_object* v_getOpenDecls_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; 
v_getCurrNamespace_2547_ = lean_ctor_get(v_inst_2525_, 0);
lean_inc(v_getCurrNamespace_2547_);
v_getOpenDecls_2548_ = lean_ctor_get(v_inst_2525_, 1);
lean_inc(v_getOpenDecls_2548_);
lean_dec_ref(v_inst_2525_);
lean_inc(v_toBind_2537_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 23, 22);
lean_closure_set(v___f_2549_, 0, v_toMonadRef_2526_);
lean_closure_set(v___f_2549_, 1, v_env_2527_);
lean_closure_set(v___f_2549_, 2, v_opts_2546_);
lean_closure_set(v___f_2549_, 3, v___x_2528_);
lean_closure_set(v___f_2549_, 4, v___f_2529_);
lean_closure_set(v___f_2549_, 5, v___f_2530_);
lean_closure_set(v___f_2549_, 6, v_toMonadQuotation_2531_);
lean_closure_set(v___f_2549_, 7, v_inst_2532_);
lean_closure_set(v___f_2549_, 8, v_x_2533_);
lean_closure_set(v___f_2549_, 9, v_toPure_2534_);
lean_closure_set(v___f_2549_, 10, v_inst_2535_);
lean_closure_set(v___f_2549_, 11, v___f_2536_);
lean_closure_set(v___f_2549_, 12, v_toBind_2537_);
lean_closure_set(v___f_2549_, 13, v_setNextMacroScope_2538_);
lean_closure_set(v___f_2549_, 14, v_inst_2539_);
lean_closure_set(v___f_2549_, 15, v_inst_2540_);
lean_closure_set(v___f_2549_, 16, v_inst_2541_);
lean_closure_set(v___f_2549_, 17, v_inst_2542_);
lean_closure_set(v___f_2549_, 18, v_inst_2543_);
lean_closure_set(v___f_2549_, 19, v_toMonadExceptOf_2544_);
lean_closure_set(v___f_2549_, 20, v_getNextMacroScope_2545_);
lean_closure_set(v___f_2549_, 21, v_getOpenDecls_2548_);
v___x_2550_ = lean_apply_4(v_toBind_2537_, lean_box(0), lean_box(0), v_getCurrNamespace_2547_, v___f_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_inst_2551_ = _args[0];
lean_object* v_toMonadRef_2552_ = _args[1];
lean_object* v_env_2553_ = _args[2];
lean_object* v___x_2554_ = _args[3];
lean_object* v___f_2555_ = _args[4];
lean_object* v___f_2556_ = _args[5];
lean_object* v_toMonadQuotation_2557_ = _args[6];
lean_object* v_inst_2558_ = _args[7];
lean_object* v_x_2559_ = _args[8];
lean_object* v_toPure_2560_ = _args[9];
lean_object* v_inst_2561_ = _args[10];
lean_object* v___f_2562_ = _args[11];
lean_object* v_toBind_2563_ = _args[12];
lean_object* v_setNextMacroScope_2564_ = _args[13];
lean_object* v_inst_2565_ = _args[14];
lean_object* v_inst_2566_ = _args[15];
lean_object* v_inst_2567_ = _args[16];
lean_object* v_inst_2568_ = _args[17];
lean_object* v_inst_2569_ = _args[18];
lean_object* v_toMonadExceptOf_2570_ = _args[19];
lean_object* v_getNextMacroScope_2571_ = _args[20];
lean_object* v_opts_2572_ = _args[21];
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_inst_2551_, v_toMonadRef_2552_, v_env_2553_, v___x_2554_, v___f_2555_, v___f_2556_, v_toMonadQuotation_2557_, v_inst_2558_, v_x_2559_, v_toPure_2560_, v_inst_2561_, v___f_2562_, v_toBind_2563_, v_setNextMacroScope_2564_, v_inst_2565_, v_inst_2566_, v_inst_2567_, v_inst_2568_, v_inst_2569_, v_toMonadExceptOf_2570_, v_getNextMacroScope_2571_, v_opts_2572_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v___x_2574_, lean_object* v___x_2575_, lean_object* v_inst_2576_, lean_object* v_toMonadRef_2577_, lean_object* v___x_2578_, lean_object* v_toMonadQuotation_2579_, lean_object* v_inst_2580_, lean_object* v_x_2581_, lean_object* v_toPure_2582_, lean_object* v_inst_2583_, lean_object* v___f_2584_, lean_object* v_toBind_2585_, lean_object* v_setNextMacroScope_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_toMonadExceptOf_2592_, lean_object* v_getNextMacroScope_2593_, lean_object* v_env_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; 
lean_inc_ref(v_env_2594_);
v___f_2595_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2595_, 0, v_env_2594_);
lean_closure_set(v___f_2595_, 1, v___x_2574_);
lean_closure_set(v___f_2595_, 2, v___x_2575_);
lean_inc_ref(v_env_2594_);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2596_, 0, v_env_2594_);
lean_inc(v_inst_2589_);
lean_inc(v_toBind_2585_);
v___f_2597_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 22, 21);
lean_closure_set(v___f_2597_, 0, v_inst_2576_);
lean_closure_set(v___f_2597_, 1, v_toMonadRef_2577_);
lean_closure_set(v___f_2597_, 2, v_env_2594_);
lean_closure_set(v___f_2597_, 3, v___x_2578_);
lean_closure_set(v___f_2597_, 4, v___f_2595_);
lean_closure_set(v___f_2597_, 5, v___f_2596_);
lean_closure_set(v___f_2597_, 6, v_toMonadQuotation_2579_);
lean_closure_set(v___f_2597_, 7, v_inst_2580_);
lean_closure_set(v___f_2597_, 8, v_x_2581_);
lean_closure_set(v___f_2597_, 9, v_toPure_2582_);
lean_closure_set(v___f_2597_, 10, v_inst_2583_);
lean_closure_set(v___f_2597_, 11, v___f_2584_);
lean_closure_set(v___f_2597_, 12, v_toBind_2585_);
lean_closure_set(v___f_2597_, 13, v_setNextMacroScope_2586_);
lean_closure_set(v___f_2597_, 14, v_inst_2587_);
lean_closure_set(v___f_2597_, 15, v_inst_2588_);
lean_closure_set(v___f_2597_, 16, v_inst_2589_);
lean_closure_set(v___f_2597_, 17, v_inst_2590_);
lean_closure_set(v___f_2597_, 18, v_inst_2591_);
lean_closure_set(v___f_2597_, 19, v_toMonadExceptOf_2592_);
lean_closure_set(v___f_2597_, 20, v_getNextMacroScope_2593_);
v___x_2598_ = lean_apply_4(v_toBind_2585_, lean_box(0), lean_box(0), v_inst_2589_, v___f_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v___x_2599_ = _args[0];
lean_object* v___x_2600_ = _args[1];
lean_object* v_inst_2601_ = _args[2];
lean_object* v_toMonadRef_2602_ = _args[3];
lean_object* v___x_2603_ = _args[4];
lean_object* v_toMonadQuotation_2604_ = _args[5];
lean_object* v_inst_2605_ = _args[6];
lean_object* v_x_2606_ = _args[7];
lean_object* v_toPure_2607_ = _args[8];
lean_object* v_inst_2608_ = _args[9];
lean_object* v___f_2609_ = _args[10];
lean_object* v_toBind_2610_ = _args[11];
lean_object* v_setNextMacroScope_2611_ = _args[12];
lean_object* v_inst_2612_ = _args[13];
lean_object* v_inst_2613_ = _args[14];
lean_object* v_inst_2614_ = _args[15];
lean_object* v_inst_2615_ = _args[16];
lean_object* v_inst_2616_ = _args[17];
lean_object* v_toMonadExceptOf_2617_ = _args[18];
lean_object* v_getNextMacroScope_2618_ = _args[19];
lean_object* v_env_2619_ = _args[20];
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v___x_2599_, v___x_2600_, v_inst_2601_, v_toMonadRef_2602_, v___x_2603_, v_toMonadQuotation_2604_, v_inst_2605_, v_x_2606_, v_toPure_2607_, v_inst_2608_, v___f_2609_, v_toBind_2610_, v_setNextMacroScope_2611_, v_inst_2612_, v_inst_2613_, v_inst_2614_, v_inst_2615_, v_inst_2616_, v_toMonadExceptOf_2617_, v_getNextMacroScope_2618_, v_env_2619_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_EStateM_nonBacktrackable(lean_box(0));
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2642_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___f_2644_; 
v___x_2643_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2644_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2644_, 0, v___x_2643_);
return v___f_2644_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___f_2646_; 
v___x_2645_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2646_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2646_, 0, v___x_2645_);
return v___f_2646_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; 
v___f_2647_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2648_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___f_2648_);
lean_ctor_set(v___x_2649_, 1, v___f_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v_toApplicative_2664_; lean_object* v_toBind_2665_; lean_object* v_getEnv_2666_; lean_object* v_toMonadExceptOf_2667_; lean_object* v_toMonadRef_2668_; lean_object* v_toMonadQuotation_2669_; lean_object* v_getNextMacroScope_2670_; lean_object* v_setNextMacroScope_2671_; lean_object* v_toPure_2672_; lean_object* v___x_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; 
v___x_2662_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2663_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2664_ = lean_ctor_get(v_inst_2652_, 0);
v_toBind_2665_ = lean_ctor_get(v_inst_2652_, 1);
lean_inc(v_toBind_2665_);
v_getEnv_2666_ = lean_ctor_get(v_inst_2654_, 0);
lean_inc(v_getEnv_2666_);
v_toMonadExceptOf_2667_ = lean_ctor_get(v_inst_2656_, 0);
lean_inc_ref(v_toMonadExceptOf_2667_);
v_toMonadRef_2668_ = lean_ctor_get(v_inst_2656_, 1);
lean_inc_ref(v_toMonadRef_2668_);
v_toMonadQuotation_2669_ = lean_ctor_get(v_inst_2653_, 0);
lean_inc_ref(v_toMonadQuotation_2669_);
v_getNextMacroScope_2670_ = lean_ctor_get(v_inst_2653_, 1);
lean_inc(v_getNextMacroScope_2670_);
v_setNextMacroScope_2671_ = lean_ctor_get(v_inst_2653_, 2);
lean_inc(v_setNextMacroScope_2671_);
lean_dec_ref(v_inst_2653_);
v_toPure_2672_ = lean_ctor_get(v_toApplicative_2664_, 1);
lean_inc(v_toPure_2672_);
v___x_2673_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_toBind_2665_);
lean_inc(v_inst_2659_);
lean_inc(v_inst_2660_);
lean_inc_ref(v_toMonadRef_2668_);
lean_inc_ref(v_inst_2658_);
lean_inc_ref(v_inst_2652_);
lean_inc(v_toPure_2672_);
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 8, 7);
lean_closure_set(v___f_2674_, 0, v_toPure_2672_);
lean_closure_set(v___f_2674_, 1, v_inst_2652_);
lean_closure_set(v___f_2674_, 2, v_inst_2658_);
lean_closure_set(v___f_2674_, 3, v_toMonadRef_2668_);
lean_closure_set(v___f_2674_, 4, v_inst_2660_);
lean_closure_set(v___f_2674_, 5, v_inst_2659_);
lean_closure_set(v___f_2674_, 6, v_toBind_2665_);
lean_inc(v_toBind_2665_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 21, 20);
lean_closure_set(v___f_2675_, 0, v___x_2663_);
lean_closure_set(v___f_2675_, 1, v___x_2673_);
lean_closure_set(v___f_2675_, 2, v_inst_2657_);
lean_closure_set(v___f_2675_, 3, v_toMonadRef_2668_);
lean_closure_set(v___f_2675_, 4, v___x_2662_);
lean_closure_set(v___f_2675_, 5, v_toMonadQuotation_2669_);
lean_closure_set(v___f_2675_, 6, v_inst_2655_);
lean_closure_set(v___f_2675_, 7, v_x_2661_);
lean_closure_set(v___f_2675_, 8, v_toPure_2672_);
lean_closure_set(v___f_2675_, 9, v_inst_2652_);
lean_closure_set(v___f_2675_, 10, v___f_2674_);
lean_closure_set(v___f_2675_, 11, v_toBind_2665_);
lean_closure_set(v___f_2675_, 12, v_setNextMacroScope_2671_);
lean_closure_set(v___f_2675_, 13, v_inst_2654_);
lean_closure_set(v___f_2675_, 14, v_inst_2658_);
lean_closure_set(v___f_2675_, 15, v_inst_2659_);
lean_closure_set(v___f_2675_, 16, v_inst_2660_);
lean_closure_set(v___f_2675_, 17, v_inst_2656_);
lean_closure_set(v___f_2675_, 18, v_toMonadExceptOf_2667_);
lean_closure_set(v___f_2675_, 19, v_getNextMacroScope_2670_);
v___x_2676_ = lean_apply_4(v_toBind_2665_, lean_box(0), lean_box(0), v_getEnv_2666_, v___f_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2677_, lean_object* v_00_u03b1_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_inst_2684_, v_inst_2685_, v_inst_2686_, v_inst_2687_, v_x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2691_, lean_object* v_00_u03b1_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_x_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Elab_liftMacroM(v_m_2691_, v_00_u03b1_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_x_2703_);
lean_dec(v_inst_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_x_2714_, lean_object* v_stx_2715_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_apply_1(v_x_2714_, v_stx_2715_);
v___x_2717_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_inst_2712_, v_inst_2713_, v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_x_2729_, lean_object* v_stx_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_apply_1(v_x_2729_, v_stx_2730_);
v___x_2732_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_inst_2725_, v_inst_2726_, v_inst_2727_, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_x_2744_, lean_object* v_stx_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Elab_adaptMacro(v_m_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_x_2744_, v_stx_2745_);
lean_dec(v_inst_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2747_, lean_object* v_currNamespace_2748_, lean_object* v_idx_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_name_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_inc(v_idx_2749_);
lean_inc(v_baseName_2747_);
v_name_2752_ = lean_name_append_index_after(v_baseName_2747_, v_idx_2749_);
lean_inc(v_name_2752_);
lean_inc(v_currNamespace_2748_);
v___x_2753_ = l_Lean_Name_append(v_currNamespace_2748_, v_name_2752_);
lean_inc_ref(v_a_2750_);
v___x_2754_ = l_Lean_Macro_hasDecl(v___x_2753_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; uint8_t v___x_2756_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
v___x_2756_ = lean_unbox(v_a_2755_);
lean_dec(v_a_2755_);
if (v___x_2756_ == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_a_2750_);
lean_dec(v_idx_2749_);
lean_dec(v_currNamespace_2748_);
lean_dec(v_baseName_2747_);
v_a_2757_ = lean_ctor_get(v___x_2754_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; 
v_unused_2765_ = lean_ctor_get(v___x_2754_, 0);
lean_dec(v_unused_2765_);
v___x_2759_ = v___x_2754_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2754_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v_name_2752_);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_name_2752_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v_name_2752_);
v_a_2766_ = lean_ctor_get(v___x_2754_, 1);
lean_inc(v_a_2766_);
lean_dec_ref(v___x_2754_);
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = lean_nat_add(v_idx_2749_, v___x_2767_);
lean_dec(v_idx_2749_);
v_idx_2749_ = v___x_2768_;
v_a_2751_ = v_a_2766_;
goto _start;
}
}
else
{
lean_object* v_a_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_name_2752_);
lean_dec_ref(v_a_2750_);
lean_dec(v_idx_2749_);
lean_dec(v_currNamespace_2748_);
lean_dec(v_baseName_2747_);
v_a_2770_ = lean_ctor_get(v___x_2754_, 0);
v_a_2771_ = lean_ctor_get(v___x_2754_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2754_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
lean_dec(v___x_2754_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2770_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2782_; 
lean_inc_ref(v_a_2780_);
v___x_2782_ = l_Lean_Macro_getCurrNamespace(v_a_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
v_a_2784_ = lean_ctor_get(v___x_2782_, 1);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2782_);
lean_inc(v_baseName_2779_);
lean_inc(v_a_2783_);
v___x_2785_ = l_Lean_Name_append(v_a_2783_, v_baseName_2779_);
lean_inc_ref(v_a_2780_);
v___x_2786_ = l_Lean_Macro_hasDecl(v___x_2785_, v_a_2780_, v_a_2784_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; uint8_t v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
v___x_2788_ = lean_unbox(v_a_2787_);
lean_dec(v_a_2787_);
if (v___x_2788_ == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2780_);
v_a_2789_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2797_);
v___x_2791_ = v___x_2786_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2786_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v_baseName_2779_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_baseName_2779_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2786_);
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2779_, v_a_2783_, v___x_2799_, v_a_2780_, v_a_2798_);
return v___x_2800_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2780_);
lean_dec(v_baseName_2779_);
v_a_2801_ = lean_ctor_get(v___x_2786_, 0);
v_a_2802_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2786_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_inc(v_a_2801_);
lean_dec(v___x_2786_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2801_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_dec_ref(v_a_2780_);
lean_dec(v_baseName_2779_);
return v___x_2782_;
}
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_name_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2818_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2819_ = l_Lean_MessageData_ofName(v_name_2817_);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = l_Lean_logError___redArg(v_inst_2813_, v_inst_2814_, v_inst_2815_, v_inst_2816_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_ex_2827_){
_start:
{
if (lean_obj_tag(v_ex_2827_) == 0)
{
lean_object* v_ref_2828_; lean_object* v_msg_2829_; lean_object* v___x_2830_; 
lean_dec(v_inst_2826_);
v_ref_2828_ = lean_ctor_get(v_ex_2827_, 0);
lean_inc(v_ref_2828_);
v_msg_2829_ = lean_ctor_get(v_ex_2827_, 1);
lean_inc_ref(v_msg_2829_);
lean_dec_ref(v_ex_2827_);
v___x_2830_ = l_Lean_logErrorAt___redArg(v_inst_2822_, v_inst_2823_, v_inst_2824_, v_inst_2825_, v_ref_2828_, v_msg_2829_);
return v___x_2830_;
}
else
{
lean_object* v_id_2831_; lean_object* v___f_2832_; uint8_t v___y_2834_; uint8_t v___x_2843_; 
v_id_2831_ = lean_ctor_get(v_ex_2827_, 0);
lean_inc(v_id_2831_);
lean_inc_ref(v_inst_2822_);
v___f_2832_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2832_, 0, v_inst_2822_);
lean_closure_set(v___f_2832_, 1, v_inst_2823_);
lean_closure_set(v___f_2832_, 2, v_inst_2824_);
lean_closure_set(v___f_2832_, 3, v_inst_2825_);
v___x_2843_ = l_Lean_Elab_isAbortExceptionId(v_id_2831_);
if (v___x_2843_ == 0)
{
uint8_t v___x_2844_; 
v___x_2844_ = l_Lean_Exception_isInterrupt(v_ex_2827_);
lean_dec_ref(v_ex_2827_);
v___y_2834_ = v___x_2844_;
goto v___jp_2833_;
}
else
{
lean_dec_ref(v_ex_2827_);
v___y_2834_ = v___x_2843_;
goto v___jp_2833_;
}
v___jp_2833_:
{
if (v___y_2834_ == 0)
{
lean_object* v_toBind_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_toBind_2835_ = lean_ctor_get(v_inst_2822_, 1);
lean_inc(v_toBind_2835_);
lean_dec_ref(v_inst_2822_);
v___x_2836_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2836_, 0, v_id_2831_);
v___x_2837_ = lean_apply_2(v_inst_2826_, lean_box(0), v___x_2836_);
v___x_2838_ = lean_apply_4(v_toBind_2835_, lean_box(0), lean_box(0), v___x_2837_, v___f_2832_);
return v___x_2838_;
}
else
{
lean_object* v_toApplicative_2839_; lean_object* v_toPure_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec_ref(v___f_2832_);
lean_dec(v_id_2831_);
lean_dec(v_inst_2826_);
v_toApplicative_2839_ = lean_ctor_get(v_inst_2822_, 0);
lean_inc_ref(v_toApplicative_2839_);
lean_dec_ref(v_inst_2822_);
v_toPure_2840_ = lean_ctor_get(v_toApplicative_2839_, 1);
lean_inc(v_toPure_2840_);
lean_dec_ref(v_toApplicative_2839_);
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_apply_2(v_toPure_2840_, lean_box(0), v___x_2841_);
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2845_, lean_object* v_inst_2846_, lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_ex_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Elab_logException___redArg(v_inst_2846_, v_inst_2847_, v_inst_2848_, v_inst_2849_, v_inst_2850_, v_ex_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_ex_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Elab_logException___redArg(v_inst_2853_, v_inst_2854_, v_inst_2855_, v_inst_2856_, v_inst_2857_, v_ex_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v_tryCatch_2867_; lean_object* v___f_2868_; lean_object* v___x_2869_; 
v_tryCatch_2867_ = lean_ctor_get(v_inst_2862_, 1);
lean_inc(v_tryCatch_2867_);
lean_dec_ref(v_inst_2862_);
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2868_, 0, v_inst_2860_);
lean_closure_set(v___f_2868_, 1, v_inst_2861_);
lean_closure_set(v___f_2868_, 2, v_inst_2863_);
lean_closure_set(v___f_2868_, 3, v_inst_2864_);
lean_closure_set(v___f_2868_, 4, v_inst_2865_);
v___x_2869_ = lean_apply_3(v_tryCatch_2867_, lean_box(0), v_x_2866_, v___f_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Elab_withLogging___redArg(v_inst_2871_, v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_inst_2876_, v_x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2882_, lean_object* v_ex_2883_, lean_object* v_toPure_2884_, lean_object* v_____do__lift_2885_){
_start:
{
lean_object* v_exPosition_2886_; lean_object* v_line_2887_; lean_object* v_column_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2908_; 
v_exPosition_2886_ = l_Lean_FileMap_toPosition(v_____do__lift_2885_, v_val_2882_);
v_line_2887_ = lean_ctor_get(v_exPosition_2886_, 0);
v_column_2888_ = lean_ctor_get(v_exPosition_2886_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_exPosition_2886_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2890_ = v_exPosition_2886_;
v_isShared_2891_ = v_isSharedCheck_2908_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_column_2888_);
lean_inc(v_line_2887_);
lean_dec(v_exPosition_2886_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2908_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2892_ = l_Nat_reprFast(v_line_2887_);
v___x_2893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofFormat(v___x_2893_);
v___x_2895_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 7);
lean_ctor_set(v___x_2890_, 1, v___x_2895_);
lean_ctor_set(v___x_2890_, 0, v___x_2894_);
v___x_2897_ = v___x_2890_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2898_ = l_Nat_reprFast(v_column_2888_);
v___x_2899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = l_Lean_MessageData_ofFormat(v___x_2899_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2897_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = l_Lean_Exception_toMessageData(v_ex_2883_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_apply_2(v_toPure_2884_, lean_box(0), v___x_2905_);
return v___x_2906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2909_, lean_object* v_ex_2910_, lean_object* v_toPure_2911_, lean_object* v_____do__lift_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2909_, v_ex_2910_, v_toPure_2911_, v_____do__lift_2912_);
lean_dec(v_val_2909_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2914_, lean_object* v_toPure_2915_, lean_object* v_inst_2916_, lean_object* v_toBind_2917_, lean_object* v_pos_2918_){
_start:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_Exception_getRef(v_ex_2914_);
v___x_2920_ = 0;
v___x_2921_ = l_Lean_Syntax_getPos_x3f(v___x_2919_, v___x_2920_);
lean_dec(v___x_2919_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_dec(v_toBind_2917_);
lean_dec_ref(v_inst_2916_);
v___x_2922_ = l_Lean_Exception_toMessageData(v_ex_2914_);
v___x_2923_ = lean_apply_2(v_toPure_2915_, lean_box(0), v___x_2922_);
return v___x_2923_;
}
else
{
lean_object* v_val_2924_; uint8_t v___x_2925_; 
v_val_2924_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_val_2924_);
lean_dec_ref(v___x_2921_);
v___x_2925_ = lean_nat_dec_eq(v_pos_2918_, v_val_2924_);
if (v___x_2925_ == 0)
{
lean_object* v_toMonadFileMap_2926_; lean_object* v___f_2927_; lean_object* v___x_2928_; 
v_toMonadFileMap_2926_ = lean_ctor_get(v_inst_2916_, 0);
lean_inc(v_toMonadFileMap_2926_);
lean_dec_ref(v_inst_2916_);
v___f_2927_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2927_, 0, v_val_2924_);
lean_closure_set(v___f_2927_, 1, v_ex_2914_);
lean_closure_set(v___f_2927_, 2, v_toPure_2915_);
v___x_2928_ = lean_apply_4(v_toBind_2917_, lean_box(0), lean_box(0), v_toMonadFileMap_2926_, v___f_2927_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v_val_2924_);
lean_dec(v_toBind_2917_);
lean_dec_ref(v_inst_2916_);
v___x_2929_ = l_Lean_Exception_toMessageData(v_ex_2914_);
v___x_2930_ = lean_apply_2(v_toPure_2915_, lean_box(0), v___x_2929_);
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2931_, lean_object* v_toPure_2932_, lean_object* v_inst_2933_, lean_object* v_toBind_2934_, lean_object* v_pos_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2931_, v_toPure_2932_, v_inst_2933_, v_toBind_2934_, v_pos_2935_);
lean_dec(v_pos_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_ex_2939_){
_start:
{
lean_object* v_toApplicative_2940_; lean_object* v_toBind_2941_; lean_object* v_toPure_2942_; lean_object* v___x_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; 
v_toApplicative_2940_ = lean_ctor_get(v_inst_2937_, 0);
v_toBind_2941_ = lean_ctor_get(v_inst_2937_, 1);
lean_inc(v_toBind_2941_);
v_toPure_2942_ = lean_ctor_get(v_toApplicative_2940_, 1);
lean_inc(v_toPure_2942_);
lean_inc_ref(v_inst_2938_);
v___x_2943_ = l_Lean_getRefPos___redArg(v_inst_2937_, v_inst_2938_);
lean_inc(v_toBind_2941_);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2944_, 0, v_ex_2939_);
lean_closure_set(v___f_2944_, 1, v_toPure_2942_);
lean_closure_set(v___f_2944_, 2, v_inst_2938_);
lean_closure_set(v___f_2944_, 3, v_toBind_2941_);
v___x_2945_ = lean_apply_4(v_toBind_2941_, lean_box(0), lean_box(0), v___x_2943_, v___f_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_ex_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2947_, v_inst_2948_, v_ex_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_x_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2951_, v_inst_2952_, v_x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_____do__lift_2961_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2962_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v_msg_2958_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_toMessageList(v_____do__lift_2961_);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_throwError___redArg(v_inst_2959_, v_inst_2960_, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_msg_2970_, lean_object* v_exs_2971_){
_start:
{
lean_object* v_toBind_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; size_t v_sz_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_toBind_2972_ = lean_ctor_get(v_inst_2968_, 1);
lean_inc(v_toBind_2972_);
lean_inc_ref(v_inst_2968_);
v___f_2973_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2973_, 0, v_inst_2968_);
lean_closure_set(v___f_2973_, 1, v_inst_2969_);
lean_inc_ref(v_inst_2968_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2974_, 0, v_msg_2970_);
lean_closure_set(v___f_2974_, 1, v_inst_2968_);
lean_closure_set(v___f_2974_, 2, v_inst_2967_);
v_sz_2975_ = lean_array_size(v_exs_2971_);
v___x_2976_ = ((size_t)0ULL);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2968_, v___f_2973_, v_sz_2975_, v___x_2976_, v_exs_2971_);
v___x_2978_ = lean_apply_4(v_toBind_2972_, lean_box(0), lean_box(0), v___x_2977_, v___f_2974_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2979_, lean_object* v_00_u03b1_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_msg_2984_, lean_object* v_exs_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2981_, v_inst_2982_, v_inst_2983_, v_msg_2984_, v_exs_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3054_ = 0;
v___x_3055_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3056_ = l_Lean_registerTraceClass(v___x_3053_, v___x_3054_, v___x_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v___x_3056_);
v___x_3057_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3058_ = l_Lean_registerTraceClass(v___x_3057_, v___x_3054_, v___x_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; 
lean_dec_ref(v___x_3058_);
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3060_ = 1;
v___x_3061_ = l_Lean_registerTraceClass(v___x_3059_, v___x_3060_, v___x_3055_);
return v___x_3061_;
}
else
{
return v___x_3058_;
}
}
else
{
return v___x_3056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3063_;
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
