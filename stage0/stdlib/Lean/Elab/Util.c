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
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_getRefPos___redArg(lean_object*, lean_object*);
lean_object* l_Lean_toMessageList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_name_126_, 2);
v___x_137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_137_, 0, v_name_126_);
lean_ctor_set(v___x_137_, 1, v_ref_128_);
lean_ctor_set(v___x_137_, 2, v___x_135_);
lean_ctor_set(v___x_137_, 3, v_descr_131_);
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
lean_inc_ref_n(v_toApplicative_345_, 2);
v_toBind_346_ = lean_ctor_get(v_inst_341_, 1);
lean_inc_n(v_toBind_346_, 3);
v_getEnv_347_ = lean_ctor_get(v_inst_342_, 0);
lean_inc_n(v_getEnv_347_, 3);
lean_dec_ref(v_inst_342_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_348_, 0, v_inst_341_);
lean_closure_set(v___f_348_, 1, v_inst_343_);
lean_inc_ref(v___f_348_);
lean_inc(v_k_344_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_349_, 0, v_k_344_);
lean_closure_set(v___f_349_, 1, v___f_348_);
lean_closure_set(v___f_349_, 2, v_toApplicative_345_);
lean_closure_set(v___f_349_, 3, v_toBind_346_);
lean_closure_set(v___f_349_, 4, v_getEnv_347_);
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
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
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
lean_inc_n(v_a_545_, 2);
lean_dec_ref(v___x_544_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_677_, lean_object* v___y_678_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_717_, v___y_718_);
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
v___x_741_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_740_, v___y_732_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_768_, lean_object* v_declHint_769_, lean_object* v___y_770_){
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
v___x_787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_c_785_);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
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
v___x_803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_c_785_);
v___x_805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_MessageData_ofName(v_mod_801_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
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
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_c_785_);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_MessageData_ofName(v_mod_801_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_831_, lean_object* v_declHint_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_831_, v_declHint_832_, v___y_833_);
lean_dec(v___y_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_836_, lean_object* v_declHint_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v___x_841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_836_, v_declHint_837_, v___y_839_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_852_, lean_object* v_declHint_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_852_, v_declHint_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_858_, lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_){
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_882_, lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_882_, v_msg_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v_ref_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_888_, lean_object* v_msg_889_, lean_object* v_declHint_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_a_895_; lean_object* v___x_896_; 
v___x_894_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_889_, v_declHint_890_, v___y_891_, v___y_892_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_888_, v_a_895_, v___y_891_, v___y_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_897_, lean_object* v_msg_898_, lean_object* v_declHint_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_897_, v_msg_898_, v_declHint_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v_ref_897_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_907_, lean_object* v_constName_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_912_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
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
v___x_918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_907_, v___x_917_, v_constName_908_, v___y_909_, v___y_910_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_919_, lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_919_, v_constName_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v_ref_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_ref_929_; lean_object* v___x_930_; 
v_ref_929_ = lean_ctor_get(v___y_926_, 5);
v___x_930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_929_, v_constName_925_, v___y_926_, v___y_927_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_){
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
v___x_944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_936_, v___y_937_, v___y_938_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_958_, lean_object* v_a_959_){
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
v___x_976_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_972_, v___y_973_, v___y_974_);
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
v___x_983_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_981_, v___x_982_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_res_1045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1042_, v_i_1043_, v_k_1044_);
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
v___x_1057_ = lean_box(2);
v___x_1058_ = ((size_t)5ULL);
v___x_1059_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1060_ = lean_usize_land(v_x_1054_, v___x_1059_);
v_j_1061_ = lean_usize_to_nat(v___x_1060_);
v___x_1062_ = lean_array_get_borrowed(v___x_1057_, v_es_1056_, v_j_1061_);
lean_dec(v_j_1061_);
switch(lean_obj_tag(v___x_1062_))
{
case 0:
{
lean_object* v_key_1063_; uint8_t v___x_1064_; 
v_key_1063_ = lean_ctor_get(v___x_1062_, 0);
v___x_1064_ = l_Lean_instBEqExtraModUse_beq(v_x_1055_, v_key_1063_);
return v___x_1064_;
}
case 1:
{
lean_object* v_node_1065_; size_t v___x_1066_; 
v_node_1065_ = lean_ctor_get(v___x_1062_, 0);
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
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1069_, v___x_1070_, v_x_1055_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
size_t v_x_6762__boxed_1075_; uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_x_6762__boxed_1075_ = lean_unbox_usize(v_x_1073_);
lean_dec(v_x_1073_);
v_res_1076_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1072_, v_x_6762__boxed_1075_, v_x_1074_);
lean_dec_ref(v_x_1074_);
lean_dec_ref(v_x_1072_);
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
lean_dec_ref(v_x_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1087_; double v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_float_of_nat(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1143_; 
v_ref_1097_ = lean_ctor_get(v___y_1094_, 5);
v___x_1098_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1093_, v___y_1094_, v___y_1095_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1143_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1143_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v_traceState_1104_; lean_object* v_env_1105_; lean_object* v_nextMacroScope_1106_; lean_object* v_ngen_1107_; lean_object* v_auxDeclNGen_1108_; lean_object* v_cache_1109_; lean_object* v_messages_1110_; lean_object* v_infoState_1111_; lean_object* v_snapshotTasks_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1142_; 
v___x_1103_ = lean_st_ref_take(v___y_1095_);
v_traceState_1104_ = lean_ctor_get(v___x_1103_, 4);
v_env_1105_ = lean_ctor_get(v___x_1103_, 0);
v_nextMacroScope_1106_ = lean_ctor_get(v___x_1103_, 1);
v_ngen_1107_ = lean_ctor_get(v___x_1103_, 2);
v_auxDeclNGen_1108_ = lean_ctor_get(v___x_1103_, 3);
v_cache_1109_ = lean_ctor_get(v___x_1103_, 5);
v_messages_1110_ = lean_ctor_get(v___x_1103_, 6);
v_infoState_1111_ = lean_ctor_get(v___x_1103_, 7);
v_snapshotTasks_1112_ = lean_ctor_get(v___x_1103_, 8);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1114_ = v___x_1103_;
v_isShared_1115_ = v_isSharedCheck_1142_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snapshotTasks_1112_);
lean_inc(v_infoState_1111_);
lean_inc(v_messages_1110_);
lean_inc(v_cache_1109_);
lean_inc(v_traceState_1104_);
lean_inc(v_auxDeclNGen_1108_);
lean_inc(v_ngen_1107_);
lean_inc(v_nextMacroScope_1106_);
lean_inc(v_env_1105_);
lean_dec(v___x_1103_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1142_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint64_t v_tid_1116_; lean_object* v_traces_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1141_; 
v_tid_1116_ = lean_ctor_get_uint64(v_traceState_1104_, sizeof(void*)*1);
v_traces_1117_ = lean_ctor_get(v_traceState_1104_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_traceState_1104_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1119_ = v_traceState_1104_;
v_isShared_1120_ = v_isSharedCheck_1141_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_traces_1117_);
lean_dec(v_traceState_1104_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1141_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; double v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1123_ = 0;
v___x_1124_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1125_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1125_, 0, v_cls_1092_);
lean_ctor_set(v___x_1125_, 1, v___x_1121_);
lean_ctor_set(v___x_1125_, 2, v___x_1124_);
lean_ctor_set_float(v___x_1125_, sizeof(void*)*3, v___x_1122_);
lean_ctor_set_float(v___x_1125_, sizeof(void*)*3 + 8, v___x_1122_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*3 + 16, v___x_1123_);
v___x_1126_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1127_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v_a_1099_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
lean_inc(v_ref_1097_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_ref_1097_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_PersistentArray_push___redArg(v_traces_1117_, v___x_1128_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1129_);
v___x_1131_ = v___x_1119_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1129_);
lean_ctor_set_uint64(v_reuseFailAlloc_1140_, sizeof(void*)*1, v_tid_1116_);
v___x_1131_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1131_);
v___x_1133_ = v___x_1114_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_env_1105_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_nextMacroScope_1106_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_ngen_1107_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_auxDeclNGen_1108_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 5, v_cache_1109_);
lean_ctor_set(v_reuseFailAlloc_1139_, 6, v_messages_1110_);
lean_ctor_set(v_reuseFailAlloc_1139_, 7, v_infoState_1111_);
lean_ctor_set(v_reuseFailAlloc_1139_, 8, v_snapshotTasks_1112_);
v___x_1133_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1134_ = lean_st_ref_set(v___y_1095_, v___x_1133_);
v___x_1135_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1135_);
v___x_1137_ = v___x_1101_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1144_, lean_object* v_msg_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1144_, v_msg_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1149_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1153_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1154_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_cls_1174_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1175_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1176_ = l_Lean_Name_append(v___x_1175_, v_cls_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1187_, uint8_t v_isMeta_1188_, lean_object* v_hint_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v_env_1194_; uint8_t v_isExporting_1195_; lean_object* v___x_1196_; lean_object* v_env_1197_; lean_object* v___x_1198_; lean_object* v_entry_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___y_1204_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1193_ = lean_st_ref_get(v___y_1191_);
v_env_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_env_1194_);
lean_dec(v___x_1193_);
v_isExporting_1195_ = lean_ctor_get_uint8(v_env_1194_, sizeof(void*)*8);
lean_dec_ref(v_env_1194_);
v___x_1196_ = lean_st_ref_get(v___y_1191_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_env_1197_);
lean_dec(v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1187_);
v_entry_1199_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1199_, 0, v_mod_1187_);
lean_ctor_set_uint8(v_entry_1199_, sizeof(void*)*1, v_isExporting_1195_);
lean_ctor_set_uint8(v_entry_1199_, sizeof(void*)*1 + 1, v_isMeta_1188_);
v___x_1200_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1201_ = lean_box(1);
v___x_1202_ = lean_box(0);
v___x_1229_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1198_, v___x_1200_, v_env_1197_, v___x_1201_, v___x_1202_);
v___x_1230_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1229_, v_entry_1199_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v_options_1231_; uint8_t v_hasTrace_1232_; 
v_options_1231_ = lean_ctor_get(v___y_1190_, 2);
v_hasTrace_1232_ = lean_ctor_get_uint8(v_options_1231_, sizeof(void*)*1);
if (v_hasTrace_1232_ == 0)
{
lean_dec(v_hint_1189_);
lean_dec(v_mod_1187_);
v___y_1204_ = v___y_1191_;
goto v___jp_1203_;
}
else
{
lean_object* v_inheritedTraceOptions_1233_; lean_object* v_cls_1234_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_inheritedTraceOptions_1233_ = lean_ctor_get(v___y_1190_, 13);
v_cls_1234_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1254_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
v___x_1255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1233_, v_options_1231_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_hint_1189_);
lean_dec(v_mod_1187_);
v___y_1204_ = v___y_1191_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1256_; lean_object* v___y_1258_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
if (v_isExporting_1195_ == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22));
v___y_1258_ = v___x_1265_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23));
v___y_1258_ = v___x_1266_;
goto v___jp_1257_;
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_inc_ref(v___y_1258_);
v___x_1259_ = l_Lean_stringToMessageData(v___y_1258_);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1256_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
if (v_isMeta_1188_ == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1241_ = v___x_1262_;
v___y_1242_ = v___x_1263_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21));
v___y_1241_ = v___x_1262_;
v___y_1242_ = v___x_1264_;
goto v___jp_1240_;
}
}
}
v___jp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1236_);
lean_ctor_set(v___x_1238_, 1, v___y_1237_);
v___x_1239_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1234_, v___x_1238_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref(v___x_1239_);
v___y_1204_ = v___y_1191_;
goto v___jp_1203_;
}
else
{
lean_dec_ref(v_entry_1199_);
return v___x_1239_;
}
}
v___jp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
lean_inc_ref(v___y_1242_);
v___x_1243_ = l_Lean_stringToMessageData(v___y_1242_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1241_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_MessageData_ofName(v_mod_1187_);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = l_Lean_Name_isAnonymous(v_hint_1189_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1251_ = l_Lean_MessageData_ofName(v_hint_1189_);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___y_1236_ = v___x_1248_;
v___y_1237_ = v___x_1252_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1253_; 
lean_dec(v_hint_1189_);
v___x_1253_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1236_ = v___x_1248_;
v___y_1237_ = v___x_1253_;
goto v___jp_1235_;
}
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v_entry_1199_);
lean_dec(v_hint_1189_);
lean_dec(v_mod_1187_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v_toEnvExtension_1206_; lean_object* v_env_1207_; lean_object* v_nextMacroScope_1208_; lean_object* v_ngen_1209_; lean_object* v_auxDeclNGen_1210_; lean_object* v_traceState_1211_; lean_object* v_messages_1212_; lean_object* v_infoState_1213_; lean_object* v_snapshotTasks_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1227_; 
v___x_1205_ = lean_st_ref_take(v___y_1204_);
v_toEnvExtension_1206_ = lean_ctor_get(v___x_1200_, 0);
v_env_1207_ = lean_ctor_get(v___x_1205_, 0);
v_nextMacroScope_1208_ = lean_ctor_get(v___x_1205_, 1);
v_ngen_1209_ = lean_ctor_get(v___x_1205_, 2);
v_auxDeclNGen_1210_ = lean_ctor_get(v___x_1205_, 3);
v_traceState_1211_ = lean_ctor_get(v___x_1205_, 4);
v_messages_1212_ = lean_ctor_get(v___x_1205_, 6);
v_infoState_1213_ = lean_ctor_get(v___x_1205_, 7);
v_snapshotTasks_1214_ = lean_ctor_get(v___x_1205_, 8);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1205_, 5);
lean_dec(v_unused_1228_);
v___x_1216_ = v___x_1205_;
v_isShared_1217_ = v_isSharedCheck_1227_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snapshotTasks_1214_);
lean_inc(v_infoState_1213_);
lean_inc(v_messages_1212_);
lean_inc(v_traceState_1211_);
lean_inc(v_auxDeclNGen_1210_);
lean_inc(v_ngen_1209_);
lean_inc(v_nextMacroScope_1208_);
lean_inc(v_env_1207_);
lean_dec(v___x_1205_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1227_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_asyncMode_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v_asyncMode_1218_ = lean_ctor_get(v_toEnvExtension_1206_, 2);
v___x_1219_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1200_, v_env_1207_, v_entry_1199_, v_asyncMode_1218_, v___x_1202_);
v___x_1220_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 5, v___x_1220_);
lean_ctor_set(v___x_1216_, 0, v___x_1219_);
v___x_1222_ = v___x_1216_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_nextMacroScope_1208_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_ngen_1209_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_auxDeclNGen_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_traceState_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_messages_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_infoState_1213_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_snapshotTasks_1214_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_st_ref_set(v___y_1204_, v___x_1222_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1269_, lean_object* v_isMeta_1270_, lean_object* v_hint_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_isMeta_boxed_1275_; lean_object* v_res_1276_; 
v_isMeta_boxed_1275_ = lean_unbox(v_isMeta_1270_);
v_res_1276_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1269_, v_isMeta_boxed_1275_, v_hint_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1277_, lean_object* v_declName_1278_, lean_object* v_as_1279_, size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_declName_1278_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_b_1282_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; lean_object* v_modules_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v_toImport_1293_; lean_object* v_module_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1288_ = l_Lean_Environment_header(v___x_1277_);
v_modules_1289_ = lean_ctor_get(v___x_1288_, 3);
lean_inc_ref(v_modules_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1291_ = lean_array_uget_borrowed(v_as_1279_, v_i_1281_);
v___x_1292_ = lean_array_get(v___x_1290_, v_modules_1289_, v_a_1291_);
lean_dec_ref(v_modules_1289_);
v_toImport_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_toImport_1293_);
lean_dec(v___x_1292_);
v_module_1294_ = lean_ctor_get(v_toImport_1293_, 0);
lean_inc(v_module_1294_);
lean_dec_ref(v_toImport_1293_);
v___x_1295_ = 0;
lean_inc(v_declName_1278_);
v___x_1296_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1294_, v___x_1295_, v_declName_1278_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; 
lean_dec_ref(v___x_1296_);
v___x_1297_ = lean_box(0);
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1281_, v___x_1298_);
v_i_1281_ = v___x_1299_;
v_b_1282_ = v___x_1297_;
goto _start;
}
else
{
lean_dec(v_declName_1278_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1301_, lean_object* v_declName_1302_, lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1301_, v_declName_1302_, v_as_1303_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v_as_1303_);
lean_dec_ref(v___x_1301_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1313_, lean_object* v_x_1314_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v_key_1316_; lean_object* v_value_1317_; lean_object* v_tail_1318_; uint8_t v___x_1319_; 
v_key_1316_ = lean_ctor_get(v_x_1314_, 0);
v_value_1317_ = lean_ctor_get(v_x_1314_, 1);
v_tail_1318_ = lean_ctor_get(v_x_1314_, 2);
v___x_1319_ = lean_name_eq(v_key_1316_, v_a_1313_);
if (v___x_1319_ == 0)
{
v_x_1314_ = v_tail_1318_;
goto _start;
}
else
{
lean_object* v___x_1321_; 
lean_inc(v_value_1317_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_value_1317_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1322_, v_x_1323_);
lean_dec(v_x_1323_);
lean_dec(v_a_1322_);
return v_res_1324_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1325_; uint64_t v___x_1326_; 
v___x_1325_ = lean_unsigned_to_nat(1723u);
v___x_1326_ = lean_uint64_of_nat(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_buckets_1329_; lean_object* v___x_1330_; uint64_t v___y_1332_; 
v_buckets_1329_ = lean_ctor_get(v_m_1327_, 1);
v___x_1330_ = lean_array_get_size(v_buckets_1329_);
if (lean_obj_tag(v_a_1328_) == 0)
{
uint64_t v___x_1346_; 
v___x_1346_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1332_ = v___x_1346_;
goto v___jp_1331_;
}
else
{
uint64_t v_hash_1347_; 
v_hash_1347_ = lean_ctor_get_uint64(v_a_1328_, sizeof(void*)*2);
v___y_1332_ = v_hash_1347_;
goto v___jp_1331_;
}
v___jp_1331_:
{
uint64_t v___x_1333_; uint64_t v___x_1334_; uint64_t v_fold_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; uint64_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1333_ = 32ULL;
v___x_1334_ = lean_uint64_shift_right(v___y_1332_, v___x_1333_);
v_fold_1335_ = lean_uint64_xor(v___y_1332_, v___x_1334_);
v___x_1336_ = 16ULL;
v___x_1337_ = lean_uint64_shift_right(v_fold_1335_, v___x_1336_);
v___x_1338_ = lean_uint64_xor(v_fold_1335_, v___x_1337_);
v___x_1339_ = lean_uint64_to_usize(v___x_1338_);
v___x_1340_ = lean_usize_of_nat(v___x_1330_);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_sub(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_usize_land(v___x_1339_, v___x_1342_);
v___x_1344_ = lean_array_uget_borrowed(v_buckets_1329_, v___x_1343_);
v___x_1345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1328_, v___x_1344_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_m_1348_);
return v_res_1350_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1354_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1355_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1354_, v___x_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1358_, uint8_t v_isMeta_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_env_1367_; lean_object* v___y_1369_; lean_object* v___x_1382_; 
v___x_1363_ = lean_st_ref_get(v___y_1361_);
v_env_1367_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref(v_env_1367_);
lean_dec(v___x_1363_);
v___x_1382_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1367_, v_declName_1358_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec_ref(v_env_1367_);
lean_dec(v_declName_1358_);
goto v___jp_1364_;
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1384_; lean_object* v_modules_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = l_Lean_Environment_header(v_env_1367_);
v_modules_1385_ = lean_ctor_get(v___x_1384_, 3);
lean_inc_ref(v_modules_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = lean_array_get_size(v_modules_1385_);
v___x_1387_ = lean_nat_dec_lt(v_val_1383_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v_modules_1385_);
lean_dec(v_val_1383_);
lean_dec_ref(v_env_1367_);
lean_dec(v_declName_1358_);
goto v___jp_1364_;
}
else
{
lean_object* v___x_1388_; lean_object* v_env_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___y_1393_; 
v___x_1388_ = lean_st_ref_get(v___y_1361_);
v_env_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_ref(v_env_1389_);
lean_dec(v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1391_ = lean_array_fget(v_modules_1385_, v_val_1383_);
lean_dec(v_val_1383_);
lean_dec_ref(v_modules_1385_);
if (v_isMeta_1359_ == 0)
{
lean_dec_ref(v_env_1389_);
v___y_1393_ = v_isMeta_1359_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1404_; 
lean_inc(v_declName_1358_);
v___x_1404_ = l_Lean_isMarkedMeta(v_env_1389_, v_declName_1358_);
if (v___x_1404_ == 0)
{
v___y_1393_ = v_isMeta_1359_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = 0;
v___y_1393_ = v___x_1405_;
goto v___jp_1392_;
}
}
v___jp_1392_:
{
lean_object* v_toImport_1394_; lean_object* v_module_1395_; lean_object* v___x_1396_; 
v_toImport_1394_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_toImport_1394_);
lean_dec(v___x_1391_);
v_module_1395_ = lean_ctor_get(v_toImport_1394_, 0);
lean_inc(v_module_1395_);
lean_dec_ref(v_toImport_1394_);
lean_inc(v_declName_1358_);
v___x_1396_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1395_, v___y_1393_, v_declName_1358_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v___x_1396_);
v___x_1397_ = l_Lean_indirectModUseExt;
v___x_1398_ = lean_box(1);
v___x_1399_ = lean_box(0);
lean_inc_ref(v_env_1367_);
v___x_1400_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1390_, v___x_1397_, v_env_1367_, v___x_1398_, v___x_1399_);
v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1400_, v_declName_1358_);
lean_dec(v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1369_ = v___x_1402_;
goto v___jp_1368_;
}
else
{
lean_object* v_val_1403_; 
v_val_1403_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1403_);
lean_dec_ref(v___x_1401_);
v___y_1369_ = v_val_1403_;
goto v___jp_1368_;
}
}
else
{
lean_dec_ref(v_env_1367_);
lean_dec(v_declName_1358_);
return v___x_1396_;
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
v___jp_1368_:
{
lean_object* v___x_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_box(0);
v_sz_1371_ = lean_array_size(v___y_1369_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1367_, v_declName_1358_, v___y_1369_, v_sz_1371_, v___x_1372_, v___x_1370_, v___y_1360_, v___y_1361_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v_env_1367_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1370_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1370_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1406_, lean_object* v_isMeta_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v_isMeta_boxed_1411_; lean_object* v_res_1412_; 
v_isMeta_boxed_1411_ = lean_unbox(v_isMeta_1407_);
v_res_1412_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1406_, v_isMeta_boxed_1411_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1413_, uint8_t v_x_1414_, lean_object* v_stx_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
lean_inc(v_stx_1415_);
v___x_1419_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1413_, v_stx_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1472_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1472_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1472_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v_env_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1424_ = lean_st_ref_get(v___y_1417_);
v_env_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc_ref(v_env_1425_);
lean_dec(v___x_1424_);
v___x_1426_ = 1;
lean_inc(v_a_1420_);
v___x_1427_ = l_Lean_Environment_contains(v_env_1425_, v_a_1420_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_stx_1415_);
if (v_isShared_1423_ == 0)
{
v___x_1429_ = v___x_1422_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1420_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
uint8_t v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1422_);
v___x_1431_ = 0;
lean_inc(v_a_1420_);
v___x_1432_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1420_, v___x_1431_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1463_);
v___x_1434_ = v___x_1432_;
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v___x_1432_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v_infoState_1437_; uint8_t v_enabled_1438_; 
v___x_1436_ = lean_st_ref_get(v___y_1417_);
v_infoState_1437_ = lean_ctor_get(v___x_1436_, 7);
lean_inc_ref(v_infoState_1437_);
lean_dec(v___x_1436_);
v_enabled_1438_ = lean_ctor_get_uint8(v_infoState_1437_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1437_);
if (v_enabled_1438_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_stx_1415_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v_a_1420_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1420_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_del_object(v___x_1434_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = l_Lean_Syntax_getArg(v_stx_1415_, v___x_1442_);
lean_dec(v_stx_1415_);
v___x_1444_ = lean_box(0);
lean_inc(v_a_1420_);
v___x_1445_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1443_, v_a_1420_, v___x_1444_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1453_);
v___x_1447_ = v___x_1445_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1445_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_a_1420_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1420_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1420_);
v_a_1454_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1445_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1445_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1420_);
lean_dec(v_stx_1415_);
v_a_1464_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1432_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1432_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1415_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1473_, lean_object* v_x_1474_, lean_object* v_stx_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v_x_7360__boxed_1479_; lean_object* v_res_1480_; 
v_x_7360__boxed_1479_ = lean_unbox(v_x_1474_);
v_res_1480_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1473_, v_x_7360__boxed_1479_, v_stx_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1483_, lean_object* v_attrName_1484_, lean_object* v_parserNamespace_1485_, lean_object* v_typeName_1486_, lean_object* v_kind_1487_, lean_object* v_attrDeclName_1488_){
_start:
{
lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___f_1490_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1491_, 0, v_parserNamespace_1485_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1493_ = lean_string_append(v_kind_1487_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1494_, 0, v_attrBuiltinName_1483_);
lean_ctor_set(v___x_1494_, 1, v_attrName_1484_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
lean_ctor_set(v___x_1494_, 3, v_typeName_1486_);
lean_ctor_set(v___x_1494_, 4, v___f_1491_);
lean_ctor_set(v___x_1494_, 5, v___f_1490_);
v___x_1495_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1494_, v_attrDeclName_1488_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1496_, lean_object* v_attrName_1497_, lean_object* v_parserNamespace_1498_, lean_object* v_typeName_1499_, lean_object* v_kind_1500_, lean_object* v_attrDeclName_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1496_, v_attrName_1497_, v_parserNamespace_1498_, v_typeName_1499_, v_kind_1500_, v_attrDeclName_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1504_, lean_object* v_attrBuiltinName_1505_, lean_object* v_attrName_1506_, lean_object* v_parserNamespace_1507_, lean_object* v_typeName_1508_, lean_object* v_kind_1509_, lean_object* v_attrDeclName_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1505_, v_attrName_1506_, v_parserNamespace_1507_, v_typeName_1508_, v_kind_1509_, v_attrDeclName_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1513_, lean_object* v_attrBuiltinName_1514_, lean_object* v_attrName_1515_, lean_object* v_parserNamespace_1516_, lean_object* v_typeName_1517_, lean_object* v_kind_1518_, lean_object* v_attrDeclName_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1513_, v_attrBuiltinName_1514_, v_attrName_1515_, v_parserNamespace_1516_, v_typeName_1517_, v_kind_1518_, v_attrDeclName_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1523_, v_a_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1526_, lean_object* v_m_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1526_, v_m_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_m_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1530_, v___y_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1539_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
uint8_t v_res_1547_; lean_object* v_r_1548_; 
v_res_1547_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1544_, v_x_1545_, v_x_1546_);
lean_dec_ref(v_x_1546_);
lean_dec_ref(v_x_1545_);
v_r_1548_ = lean_box(v_res_1547_);
return v_r_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1549_, lean_object* v_a_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1550_, v_x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1553_, lean_object* v_a_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1553_, v_a_1554_, v_x_1555_);
lean_dec(v_x_1555_);
lean_dec(v_a_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1557_, lean_object* v_x_1558_, size_t v_x_1559_, lean_object* v_x_1560_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1558_, v_x_1559_, v_x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
size_t v_x_7530__boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_x_7530__boxed_1566_ = lean_unbox_usize(v_x_1564_);
lean_dec(v_x_1564_);
v_res_1567_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1562_, v_x_1563_, v_x_7530__boxed_1566_, v_x_1565_);
lean_dec_ref(v_x_1565_);
lean_dec_ref(v_x_1563_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1569_, lean_object* v_constName_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1570_, v___y_1571_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_constName_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1575_, v_constName_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1581_, lean_object* v_keys_1582_, lean_object* v_vals_1583_, lean_object* v_heq_1584_, lean_object* v_i_1585_, lean_object* v_k_1586_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1582_, v_i_1585_, v_k_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1588_, lean_object* v_keys_1589_, lean_object* v_vals_1590_, lean_object* v_heq_1591_, lean_object* v_i_1592_, lean_object* v_k_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1588_, v_keys_1589_, v_vals_1590_, v_heq_1591_, v_i_1592_, v_k_1593_);
lean_dec_ref(v_k_1593_);
lean_dec_ref(v_vals_1590_);
lean_dec_ref(v_keys_1589_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1596_, lean_object* v_ref_1597_, lean_object* v_constName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1597_, v_constName_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_ref_1604_, lean_object* v_constName_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1603_, v_ref_1604_, v_constName_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v_ref_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1610_, lean_object* v_ref_1611_, lean_object* v_msg_1612_, lean_object* v_declHint_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1611_, v_msg_1612_, v_declHint_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_ref_1619_, lean_object* v_msg_1620_, lean_object* v_declHint_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1618_, v_ref_1619_, v_msg_1620_, v_declHint_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_ref_1619_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1626_, lean_object* v_declHint_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1626_, v_declHint_1627_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1632_, lean_object* v_declHint_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1632_, v_declHint_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1638_, lean_object* v_ref_1639_, lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1639_, v_msg_1640_, v___y_1641_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_ref_1646_, lean_object* v_msg_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1645_, v_ref_1646_, v_msg_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v_ref_1646_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1664_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1665_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1666_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1667_ = lean_box(0);
v___x_1668_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1669_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1664_, v___x_1666_, v___x_1667_, v___x_1668_, v___x_1665_, v_ref_1662_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1680_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1686_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1687_ = l_Lean_addBuiltinDocString(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((lean_object*)(l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1717_ = ((lean_object*)(l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1718_ = l_Lean_addBuiltinDeclarationRanges(v___x_1716_, v___x_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1721_, lean_object* v_a_1722_, lean_object* v_____r_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_declName_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1737_; 
v_declName_1726_ = lean_ctor_get(v_toOLeanEntry_1721_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_toOLeanEntry_1721_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v_toOLeanEntry_1721_, 0);
lean_dec(v_unused_1738_);
v___x_1728_ = v_toOLeanEntry_1721_;
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_declName_1726_);
lean_dec(v_toOLeanEntry_1721_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1722_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1730_);
lean_ctor_set(v___x_1728_, 0, v_declName_1726_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_declName_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___y_1725_);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1739_, lean_object* v_a_1740_, lean_object* v_____r_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1739_, v_a_1740_, v_____r_1741_, v___y_1742_, v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1748_, lean_object* v_as_x27_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
if (lean_obj_tag(v_as_x27_1749_) == 0)
{
lean_object* v___x_1753_; 
lean_dec(v_stx_1748_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1750_);
lean_ctor_set(v___x_1753_, 1, v___y_1752_);
return v___x_1753_;
}
else
{
lean_object* v_head_1754_; lean_object* v_tail_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_b_1750_);
v_head_1754_ = lean_ctor_get(v_as_x27_1749_, 0);
v_tail_1755_ = lean_ctor_get(v_as_x27_1749_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_as_x27_1749_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1757_ = v_as_x27_1749_;
v_isShared_1758_ = v_isSharedCheck_1833_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_tail_1755_);
lean_inc(v_head_1754_);
lean_dec(v_as_x27_1749_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1833_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_toOLeanEntry_1759_; uint8_t v_isBuiltin_1760_; lean_object* v_value_1761_; lean_object* v_macroScope_1762_; lean_object* v_traceMsgs_1763_; lean_object* v_expandedMacroDecls_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1832_; 
v_toOLeanEntry_1759_ = lean_ctor_get(v_head_1754_, 0);
lean_inc_ref(v_toOLeanEntry_1759_);
v_isBuiltin_1760_ = lean_ctor_get_uint8(v_head_1754_, sizeof(void*)*2);
v_value_1761_ = lean_ctor_get(v_head_1754_, 1);
lean_inc(v_value_1761_);
lean_dec(v_head_1754_);
v_macroScope_1762_ = lean_ctor_get(v___y_1752_, 0);
v_traceMsgs_1763_ = lean_ctor_get(v___y_1752_, 1);
v_expandedMacroDecls_1764_ = lean_ctor_get(v___y_1752_, 2);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___y_1752_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1766_ = v___y_1752_;
v_isShared_1767_ = v_isSharedCheck_1832_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_expandedMacroDecls_1764_);
lean_inc(v_traceMsgs_1763_);
lean_inc(v_macroScope_1762_);
lean_dec(v___y_1752_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1832_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_methods_1768_; lean_object* v_quotContext_1769_; lean_object* v_currRecDepth_1770_; lean_object* v_maxRecDepth_1771_; lean_object* v_ref_1772_; lean_object* v___x_1773_; lean_object* v_a_1775_; lean_object* v_a_1776_; lean_object* v___x_1780_; lean_object* v_a_1782_; lean_object* v_a_1783_; lean_object* v___y_1797_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v_methods_1768_ = lean_ctor_get(v___y_1751_, 0);
v_quotContext_1769_ = lean_ctor_get(v___y_1751_, 1);
v_currRecDepth_1770_ = lean_ctor_get(v___y_1751_, 3);
v_maxRecDepth_1771_ = lean_ctor_get(v___y_1751_, 4);
v_ref_1772_ = lean_ctor_get(v___y_1751_, 5);
v___x_1773_ = lean_box(0);
v___x_1780_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_add(v_macroScope_1762_, v___x_1803_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1804_);
v___x_1806_ = v___x_1766_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_traceMsgs_1763_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_expandedMacroDecls_1764_);
v___x_1806_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1805_;
}
v___jp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_a_1775_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v___x_1773_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_a_1776_);
return v___x_1779_;
}
v___jp_1781_:
{
if (lean_obj_tag(v_a_1782_) == 1)
{
lean_dec_ref(v_toOLeanEntry_1759_);
v_as_x27_1749_ = v_tail_1755_;
v_b_1750_ = v___x_1780_;
v___y_1752_ = v_a_1783_;
goto _start;
}
else
{
lean_object* v_declName_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_tail_1755_);
lean_dec(v_stx_1748_);
v_declName_1785_ = lean_ctor_get(v_toOLeanEntry_1759_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_toOLeanEntry_1759_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_toOLeanEntry_1759_, 0);
lean_dec(v_unused_1795_);
v___x_1787_ = v_toOLeanEntry_1759_;
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_declName_1785_);
lean_dec(v_toOLeanEntry_1759_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1782_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1789_);
lean_ctor_set(v___x_1787_, 0, v_declName_1785_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_declName_1785_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
v_a_1775_ = v___x_1792_;
v_a_1776_ = v_a_1783_;
goto v___jp_1774_;
}
}
}
}
v___jp_1796_:
{
lean_object* v_a_1798_; 
v_a_1798_ = lean_ctor_get(v___y_1797_, 0);
if (lean_obj_tag(v_a_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v_a_1800_; 
lean_inc_ref(v_a_1798_);
lean_dec(v_tail_1755_);
lean_dec(v_stx_1748_);
v_a_1799_ = lean_ctor_get(v___y_1797_, 1);
lean_inc(v_a_1799_);
lean_dec_ref(v___y_1797_);
v_a_1800_ = lean_ctor_get(v_a_1798_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v_a_1798_);
v_a_1775_ = v_a_1800_;
v_a_1776_ = v_a_1799_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1801_; 
v_a_1801_ = lean_ctor_get(v___y_1797_, 1);
lean_inc(v_a_1801_);
lean_dec_ref(v___y_1797_);
v_as_x27_1749_ = v_tail_1755_;
v_b_1750_ = v___x_1780_;
v___y_1752_ = v_a_1801_;
goto _start;
}
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_inc(v_ref_1772_);
lean_inc(v_maxRecDepth_1771_);
lean_inc(v_currRecDepth_1770_);
lean_inc(v_quotContext_1769_);
lean_inc(v_methods_1768_);
v___x_1807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1807_, 0, v_methods_1768_);
lean_ctor_set(v___x_1807_, 1, v_quotContext_1769_);
lean_ctor_set(v___x_1807_, 2, v_macroScope_1762_);
lean_ctor_set(v___x_1807_, 3, v_currRecDepth_1770_);
lean_ctor_set(v___x_1807_, 4, v_maxRecDepth_1771_);
lean_ctor_set(v___x_1807_, 5, v_ref_1772_);
lean_inc(v_stx_1748_);
v___x_1808_ = lean_apply_3(v_value_1761_, v_stx_1748_, v___x_1807_, v___x_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
if (v_isBuiltin_1760_ == 0)
{
lean_object* v_a_1809_; lean_object* v_a_1810_; lean_object* v_macroScope_1811_; lean_object* v_traceMsgs_1812_; lean_object* v_expandedMacroDecls_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_a_1809_);
v_a_1810_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1808_);
v_macroScope_1811_ = lean_ctor_get(v_a_1809_, 0);
v_traceMsgs_1812_ = lean_ctor_get(v_a_1809_, 1);
v_expandedMacroDecls_1813_ = lean_ctor_get(v_a_1809_, 2);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v_a_1809_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_expandedMacroDecls_1813_);
lean_inc(v_traceMsgs_1812_);
lean_inc(v_macroScope_1811_);
lean_dec(v_a_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_declName_1817_; lean_object* v___x_1819_; 
v_declName_1817_ = lean_ctor_get(v_toOLeanEntry_1759_, 1);
lean_inc(v_declName_1817_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v_expandedMacroDecls_1813_);
lean_ctor_set(v___x_1757_, 0, v_declName_1817_);
v___x_1819_ = v___x_1757_;
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
v___x_1822_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1759_, v_a_1810_, v___x_1773_, v___y_1751_, v___x_1821_);
v___y_1797_ = v___x_1822_;
goto v___jp_1796_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v_a_1827_; lean_object* v___x_1828_; 
lean_del_object(v___x_1757_);
v_a_1826_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1826_);
v_a_1827_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1808_);
v___x_1828_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1759_, v_a_1826_, v___x_1773_, v___y_1751_, v_a_1827_);
v___y_1797_ = v___x_1828_;
goto v___jp_1796_;
}
}
else
{
lean_object* v_a_1829_; lean_object* v_a_1830_; 
lean_del_object(v___x_1757_);
v_a_1829_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1829_);
v_a_1830_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1808_);
v_a_1782_ = v_a_1829_;
v_a_1783_ = v_a_1830_;
goto v___jp_1781_;
}
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
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
v_fst_1851_ = lean_ctor_get(v_a_1850_, 0);
lean_inc(v_fst_1851_);
lean_dec(v_a_1850_);
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
lean_dec_ref(v_fst_1851_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1929_, lean_object* v_snd_1930_, lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_toMonadRef_1933_, lean_object* v_inst_1934_, lean_object* v_fst_1935_, uint8_t v_____do__lift_1936_){
_start:
{
if (v_____do__lift_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v_fst_1935_);
lean_dec(v_inst_1934_);
lean_dec_ref(v_toMonadRef_1933_);
lean_dec_ref(v_inst_1932_);
lean_dec_ref(v_inst_1931_);
lean_dec_ref(v_snd_1930_);
v___x_1937_ = lean_box(0);
v___x_1938_ = lean_apply_2(v_toPure_1929_, lean_box(0), v___x_1937_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v_toPure_1929_);
v___x_1939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_snd_1930_);
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
v___x_1941_ = l_Lean_addTrace___redArg(v_inst_1931_, v_inst_1932_, v_toMonadRef_1933_, v_inst_1934_, v_fst_1935_, v___x_1940_);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1942_, lean_object* v_snd_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_toMonadRef_1946_, lean_object* v_inst_1947_, lean_object* v_fst_1948_, lean_object* v_____do__lift_1949_){
_start:
{
uint8_t v_____do__lift_1416__boxed_1950_; lean_object* v_res_1951_; 
v_____do__lift_1416__boxed_1950_ = lean_unbox(v_____do__lift_1949_);
v_res_1951_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1942_, v_snd_1943_, v_inst_1944_, v_inst_1945_, v_toMonadRef_1946_, v_inst_1947_, v_fst_1948_, v_____do__lift_1416__boxed_1950_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1952_, lean_object* v_fst_1953_, lean_object* v_____do__lift_1954_, lean_object* v_____do__lift_1955_){
_start:
{
uint8_t v_hasTrace_1956_; 
v_hasTrace_1956_ = lean_ctor_get_uint8(v_____do__lift_1955_, sizeof(void*)*1);
if (v_hasTrace_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_fst_1953_);
v___x_1957_ = lean_box(v_hasTrace_1956_);
v___x_1958_ = lean_apply_2(v_toPure_1952_, lean_box(0), v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1960_ = l_Lean_Name_append(v___x_1959_, v_fst_1953_);
v___x_1961_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1954_, v_____do__lift_1955_, v___x_1960_);
lean_dec(v___x_1960_);
v___x_1962_ = lean_box(v___x_1961_);
v___x_1963_ = lean_apply_2(v_toPure_1952_, lean_box(0), v___x_1962_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(lean_object* v_toPure_1964_, lean_object* v_fst_1965_, lean_object* v_____do__lift_1966_, lean_object* v_____do__lift_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Elab_liftMacroM___redArg___lam__1(v_toPure_1964_, v_fst_1965_, v_____do__lift_1966_, v_____do__lift_1967_);
lean_dec_ref(v_____do__lift_1967_);
lean_dec_ref(v_____do__lift_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1969_, lean_object* v_fst_1970_, lean_object* v_toBind_1971_, lean_object* v_inst_1972_, lean_object* v_____do__lift_1973_){
_start:
{
lean_object* v___f_1974_; lean_object* v___x_1975_; 
v___f_1974_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1974_, 0, v_toPure_1969_);
lean_closure_set(v___f_1974_, 1, v_fst_1970_);
lean_closure_set(v___f_1974_, 2, v_____do__lift_1973_);
v___x_1975_ = lean_apply_4(v_toBind_1971_, lean_box(0), lean_box(0), v_inst_1972_, v___f_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1976_, lean_object* v_toPure_1977_, lean_object* v_inst_1978_, lean_object* v_toMonadRef_1979_, lean_object* v_inst_1980_, lean_object* v_toBind_1981_, lean_object* v_inst_1982_, lean_object* v_x_1983_){
_start:
{
lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v_getInheritedTraceOptions_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_fst_1984_ = lean_ctor_get(v_x_1983_, 0);
lean_inc_n(v_fst_1984_, 2);
v_snd_1985_ = lean_ctor_get(v_x_1983_, 1);
lean_inc(v_snd_1985_);
lean_dec_ref(v_x_1983_);
v_getInheritedTraceOptions_1986_ = lean_ctor_get(v_inst_1976_, 2);
lean_inc(v_getInheritedTraceOptions_1986_);
lean_inc(v_toPure_1977_);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1987_, 0, v_toPure_1977_);
lean_closure_set(v___f_1987_, 1, v_snd_1985_);
lean_closure_set(v___f_1987_, 2, v_inst_1978_);
lean_closure_set(v___f_1987_, 3, v_inst_1976_);
lean_closure_set(v___f_1987_, 4, v_toMonadRef_1979_);
lean_closure_set(v___f_1987_, 5, v_inst_1980_);
lean_closure_set(v___f_1987_, 6, v_fst_1984_);
lean_inc_n(v_toBind_1981_, 2);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1988_, 0, v_toPure_1977_);
lean_closure_set(v___f_1988_, 1, v_fst_1984_);
lean_closure_set(v___f_1988_, 2, v_toBind_1981_);
lean_closure_set(v___f_1988_, 3, v_inst_1982_);
v___x_1989_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1986_, v___f_1988_);
v___x_1990_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1989_, v___f_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_1991_, lean_object* v___x_1992_, lean_object* v___x_1993_, lean_object* v_stx_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1991_, v_stx_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
if (lean_obj_tag(v_a_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v___x_1993_);
lean_dec_ref(v___x_1992_);
v_a_1999_ = lean_ctor_get(v___x_1997_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2008_);
v___x_2001_ = v___x_1997_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_1999_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2039_; 
v_val_2009_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2011_ = v_a_1998_;
v_isShared_2012_ = v_isSharedCheck_2039_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v_a_1998_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2039_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_snd_2013_; 
v_snd_2013_ = lean_ctor_get(v_val_2009_, 1);
lean_inc(v_snd_2013_);
lean_dec(v_val_2009_);
if (lean_obj_tag(v_snd_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_2011_);
v_a_2014_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_1997_);
v_a_2015_ = lean_ctor_get(v_snd_2013_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_snd_2013_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2017_ = v_snd_2013_;
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v_snd_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_1195__overap_2021_; lean_object* v___x_2022_; 
v___x_1195__overap_2021_ = l_liftExcept___redArg(v___x_1992_, v___x_1993_, v___x_2020_);
lean_inc_ref(v___y_1995_);
v___x_2022_ = lean_apply_2(v___x_1195__overap_2021_, v___y_1995_, v_a_2014_);
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2038_; 
v_a_2025_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_1997_);
v_a_2026_ = lean_ctor_get(v_snd_2013_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_snd_2013_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2028_ = v_snd_2013_;
v_isShared_2029_ = v_isSharedCheck_2038_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v_snd_2013_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2038_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_a_2026_);
v___x_2031_ = v___x_2011_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_1199__overap_2034_; lean_object* v___x_2035_; 
v___x_1199__overap_2034_ = l_liftExcept___redArg(v___x_1992_, v___x_1993_, v___x_2033_);
lean_inc_ref(v___y_1995_);
v___x_2035_ = lean_apply_2(v___x_1199__overap_2034_, v___y_1995_, v_a_2025_);
return v___x_2035_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v___x_1993_);
lean_dec_ref(v___x_1992_);
v_a_2040_ = lean_ctor_get(v___x_1997_, 0);
v_a_2041_ = lean_ctor_get(v___x_1997_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1997_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_inc(v_a_2040_);
lean_dec(v___x_1997_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2040_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2049_, lean_object* v___x_2050_, lean_object* v___x_2051_, lean_object* v_stx_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2049_, v___x_2050_, v___x_2051_, v_stx_2052_, v___y_2053_, v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2056_, lean_object* v_declName_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
uint8_t v___x_2060_; lean_object* v_env_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; uint8_t v___x_2064_; 
v___x_2060_ = 0;
v_env_2061_ = l_Lean_Environment_setExporting(v_env_2056_, v___x_2060_);
lean_inc(v_declName_2057_);
v___x_2062_ = l_Lean_mkPrivateName(v_env_2061_, v_declName_2057_);
v___x_2063_ = 1;
lean_inc_ref(v_env_2061_);
v___x_2064_ = l_Lean_Environment_contains(v_env_2061_, v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = l_Lean_privateToUserName(v_declName_2057_);
v___x_2066_ = l_Lean_Environment_contains(v_env_2061_, v___x_2065_, v___x_2063_);
v___x_2067_ = lean_box(v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___y_2059_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_env_2061_);
lean_dec(v_declName_2057_);
v___x_2069_ = lean_box(v___x_2064_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___y_2059_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2071_, lean_object* v_declName_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2071_, v_declName_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2076_, lean_object* v_currNamespace_2077_, lean_object* v_openDecls_2078_, lean_object* v_n_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = l_Lean_ResolveName_resolveNamespace(v_env_2076_, v_currNamespace_2077_, v_openDecls_2078_, v_n_2079_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2084_, lean_object* v_currNamespace_2085_, lean_object* v_openDecls_2086_, lean_object* v_n_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2084_, v_currNamespace_2085_, v_openDecls_2086_, v_n_2087_, v___y_2088_, v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2091_, lean_object* v_opts_2092_, lean_object* v_currNamespace_2093_, lean_object* v_openDecls_2094_, lean_object* v_n_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l_Lean_ResolveName_resolveGlobalName(v_env_2091_, v_opts_2092_, v_currNamespace_2093_, v_openDecls_2094_, v_n_2095_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2100_, lean_object* v_opts_2101_, lean_object* v_currNamespace_2102_, lean_object* v_openDecls_2103_, lean_object* v_n_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2100_, v_opts_2101_, v_currNamespace_2102_, v_openDecls_2103_, v_n_2104_, v___y_2105_, v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v_opts_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2108_, lean_object* v_a_2109_, lean_object* v_____r_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_apply_2(v_toPure_2108_, lean_box(0), v_a_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2112_, lean_object* v_inst_2113_, lean_object* v___f_2114_, lean_object* v_toBind_2115_, lean_object* v___f_2116_, lean_object* v_____r_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = l_List_reverse___redArg(v_traceMsgs_2112_);
v___x_2119_ = l_List_forM___redArg(v_inst_2113_, v___x_2118_, v___f_2114_);
v___x_2120_ = lean_apply_4(v_toBind_2115_, lean_box(0), lean_box(0), v___x_2119_, v___f_2116_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2121_, lean_object* v_macroScope_2122_, lean_object* v_toBind_2123_, lean_object* v___f_2124_, lean_object* v_____s_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_apply_1(v_setNextMacroScope_2121_, v_macroScope_2122_);
v___x_2127_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v___x_2126_, v___f_2124_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2128_, lean_object* v_toPure_2129_, lean_object* v_____r_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2128_);
v___x_2132_ = lean_apply_2(v_toPure_2129_, lean_box(0), v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_toMonadRef_2137_, lean_object* v_inst_2138_, lean_object* v_toBind_2139_, lean_object* v___f_2140_, lean_object* v_a_2141_, lean_object* v_x_2142_, lean_object* v___y_2143_){
_start:
{
uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = 1;
v___x_2145_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2133_, v_inst_2134_, v_inst_2135_, v_inst_2136_, v_toMonadRef_2137_, v_inst_2138_, v_a_2141_, v___x_2144_);
v___x_2146_ = lean_apply_4(v_toBind_2139_, lean_box(0), lean_box(0), v___x_2145_, v___f_2140_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2148_, lean_object* v_____do__lift_2149_, lean_object* v_____do__lift_2150_, lean_object* v_____do__lift_2151_, lean_object* v_____do__lift_2152_, lean_object* v_____do__lift_2153_, lean_object* v_x_2154_, lean_object* v_toPure_2155_, lean_object* v_inst_2156_, lean_object* v___f_2157_, lean_object* v_toBind_2158_, lean_object* v_setNextMacroScope_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_toMonadRef_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_toMonadExceptOf_2166_, lean_object* v_____do__lift_2167_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2168_, 0, v_methods_2148_);
lean_ctor_set(v___x_2168_, 1, v_____do__lift_2149_);
lean_ctor_set(v___x_2168_, 2, v_____do__lift_2150_);
lean_ctor_set(v___x_2168_, 3, v_____do__lift_2151_);
lean_ctor_set(v___x_2168_, 4, v_____do__lift_2152_);
lean_ctor_set(v___x_2168_, 5, v_____do__lift_2153_);
v___x_2169_ = lean_box(0);
v___x_2170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2170_, 0, v_____do__lift_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_ctor_set(v___x_2170_, 2, v___x_2169_);
v___x_2171_ = lean_apply_2(v_x_2154_, v___x_2168_, v___x_2170_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_a_2173_; lean_object* v_macroScope_2174_; lean_object* v_traceMsgs_2175_; lean_object* v_expandedMacroDecls_2176_; lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref(v_toMonadExceptOf_2166_);
lean_dec_ref(v_inst_2165_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_a_2172_);
v_a_2173_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2173_);
lean_dec_ref(v___x_2171_);
v_macroScope_2174_ = lean_ctor_get(v_a_2172_, 0);
lean_inc(v_macroScope_2174_);
v_traceMsgs_2175_ = lean_ctor_get(v_a_2172_, 1);
lean_inc(v_traceMsgs_2175_);
v_expandedMacroDecls_2176_ = lean_ctor_get(v_a_2172_, 2);
lean_inc(v_expandedMacroDecls_2176_);
lean_dec(v_a_2172_);
lean_inc(v_toPure_2155_);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2177_, 0, v_toPure_2155_);
lean_closure_set(v___f_2177_, 1, v_a_2173_);
lean_inc_n(v_toBind_2158_, 3);
lean_inc_ref_n(v_inst_2156_, 2);
v___f_2178_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2178_, 0, v_traceMsgs_2175_);
lean_closure_set(v___f_2178_, 1, v_inst_2156_);
lean_closure_set(v___f_2178_, 2, v___f_2157_);
lean_closure_set(v___f_2178_, 3, v_toBind_2158_);
lean_closure_set(v___f_2178_, 4, v___f_2177_);
v___f_2179_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2179_, 0, v_setNextMacroScope_2159_);
lean_closure_set(v___f_2179_, 1, v_macroScope_2174_);
lean_closure_set(v___f_2179_, 2, v_toBind_2158_);
lean_closure_set(v___f_2179_, 3, v___f_2178_);
v___x_2180_ = lean_box(0);
v___f_2181_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2181_, 0, v___x_2180_);
lean_closure_set(v___f_2181_, 1, v_toPure_2155_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2182_, 0, v_inst_2156_);
lean_closure_set(v___f_2182_, 1, v_inst_2160_);
lean_closure_set(v___f_2182_, 2, v_inst_2161_);
lean_closure_set(v___f_2182_, 3, v_inst_2162_);
lean_closure_set(v___f_2182_, 4, v_toMonadRef_2163_);
lean_closure_set(v___f_2182_, 5, v_inst_2164_);
lean_closure_set(v___f_2182_, 6, v_toBind_2158_);
lean_closure_set(v___f_2182_, 7, v___f_2181_);
v___x_2183_ = l_List_forIn_x27_loop___redArg(v_inst_2156_, v___f_2182_, v_expandedMacroDecls_2176_, v___x_2180_);
v___x_2184_ = lean_apply_4(v_toBind_2158_, lean_box(0), lean_box(0), v___x_2183_, v___f_2179_);
return v___x_2184_;
}
else
{
lean_object* v_a_2185_; 
lean_dec(v_inst_2164_);
lean_dec_ref(v_toMonadRef_2163_);
lean_dec(v_inst_2162_);
lean_dec_ref(v_inst_2161_);
lean_dec_ref(v_inst_2160_);
lean_dec(v_setNextMacroScope_2159_);
lean_dec(v_toBind_2158_);
lean_dec(v___f_2157_);
lean_dec(v_toPure_2155_);
v_a_2185_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2171_);
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_a_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
lean_dec_ref(v_toMonadExceptOf_2166_);
v_a_2186_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_a_2186_);
v_a_2187_ = lean_ctor_get(v_a_2185_, 1);
lean_inc_ref(v_a_2187_);
lean_dec_ref(v_a_2185_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2189_ = lean_string_dec_eq(v_a_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2187_);
v___x_2191_ = l_Lean_MessageData_ofFormat(v___x_2190_);
v___x_2192_ = l_Lean_throwErrorAt___redArg(v_inst_2156_, v_inst_2165_, v_a_2186_, v___x_2191_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; 
lean_dec_ref(v_a_2187_);
lean_dec_ref(v_inst_2156_);
v___x_2193_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2165_, v_a_2186_);
return v___x_2193_;
}
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v_inst_2165_);
lean_dec_ref(v_inst_2156_);
v___x_2194_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2166_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2195_ = _args[0];
lean_object* v_____do__lift_2196_ = _args[1];
lean_object* v_____do__lift_2197_ = _args[2];
lean_object* v_____do__lift_2198_ = _args[3];
lean_object* v_____do__lift_2199_ = _args[4];
lean_object* v_____do__lift_2200_ = _args[5];
lean_object* v_x_2201_ = _args[6];
lean_object* v_toPure_2202_ = _args[7];
lean_object* v_inst_2203_ = _args[8];
lean_object* v___f_2204_ = _args[9];
lean_object* v_toBind_2205_ = _args[10];
lean_object* v_setNextMacroScope_2206_ = _args[11];
lean_object* v_inst_2207_ = _args[12];
lean_object* v_inst_2208_ = _args[13];
lean_object* v_inst_2209_ = _args[14];
lean_object* v_toMonadRef_2210_ = _args[15];
lean_object* v_inst_2211_ = _args[16];
lean_object* v_inst_2212_ = _args[17];
lean_object* v_toMonadExceptOf_2213_ = _args[18];
lean_object* v_____do__lift_2214_ = _args[19];
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2195_, v_____do__lift_2196_, v_____do__lift_2197_, v_____do__lift_2198_, v_____do__lift_2199_, v_____do__lift_2200_, v_x_2201_, v_toPure_2202_, v_inst_2203_, v___f_2204_, v_toBind_2205_, v_setNextMacroScope_2206_, v_inst_2207_, v_inst_2208_, v_inst_2209_, v_toMonadRef_2210_, v_inst_2211_, v_inst_2212_, v_toMonadExceptOf_2213_, v_____do__lift_2214_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2216_, lean_object* v_____do__lift_2217_, lean_object* v_____do__lift_2218_, lean_object* v_____do__lift_2219_, lean_object* v_____do__lift_2220_, lean_object* v_x_2221_, lean_object* v_toPure_2222_, lean_object* v_inst_2223_, lean_object* v___f_2224_, lean_object* v_toBind_2225_, lean_object* v_setNextMacroScope_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_toMonadRef_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_toMonadExceptOf_2233_, lean_object* v_getNextMacroScope_2234_, lean_object* v_____do__lift_2235_){
_start:
{
lean_object* v___f_2236_; lean_object* v___x_2237_; 
lean_inc(v_toBind_2225_);
v___f_2236_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2236_, 0, v_methods_2216_);
lean_closure_set(v___f_2236_, 1, v_____do__lift_2217_);
lean_closure_set(v___f_2236_, 2, v_____do__lift_2218_);
lean_closure_set(v___f_2236_, 3, v_____do__lift_2219_);
lean_closure_set(v___f_2236_, 4, v_____do__lift_2235_);
lean_closure_set(v___f_2236_, 5, v_____do__lift_2220_);
lean_closure_set(v___f_2236_, 6, v_x_2221_);
lean_closure_set(v___f_2236_, 7, v_toPure_2222_);
lean_closure_set(v___f_2236_, 8, v_inst_2223_);
lean_closure_set(v___f_2236_, 9, v___f_2224_);
lean_closure_set(v___f_2236_, 10, v_toBind_2225_);
lean_closure_set(v___f_2236_, 11, v_setNextMacroScope_2226_);
lean_closure_set(v___f_2236_, 12, v_inst_2227_);
lean_closure_set(v___f_2236_, 13, v_inst_2228_);
lean_closure_set(v___f_2236_, 14, v_inst_2229_);
lean_closure_set(v___f_2236_, 15, v_toMonadRef_2230_);
lean_closure_set(v___f_2236_, 16, v_inst_2231_);
lean_closure_set(v___f_2236_, 17, v_inst_2232_);
lean_closure_set(v___f_2236_, 18, v_toMonadExceptOf_2233_);
v___x_2237_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v_getNextMacroScope_2234_, v___f_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2238_ = _args[0];
lean_object* v_____do__lift_2239_ = _args[1];
lean_object* v_____do__lift_2240_ = _args[2];
lean_object* v_____do__lift_2241_ = _args[3];
lean_object* v_____do__lift_2242_ = _args[4];
lean_object* v_x_2243_ = _args[5];
lean_object* v_toPure_2244_ = _args[6];
lean_object* v_inst_2245_ = _args[7];
lean_object* v___f_2246_ = _args[8];
lean_object* v_toBind_2247_ = _args[9];
lean_object* v_setNextMacroScope_2248_ = _args[10];
lean_object* v_inst_2249_ = _args[11];
lean_object* v_inst_2250_ = _args[12];
lean_object* v_inst_2251_ = _args[13];
lean_object* v_toMonadRef_2252_ = _args[14];
lean_object* v_inst_2253_ = _args[15];
lean_object* v_inst_2254_ = _args[16];
lean_object* v_toMonadExceptOf_2255_ = _args[17];
lean_object* v_getNextMacroScope_2256_ = _args[18];
lean_object* v_____do__lift_2257_ = _args[19];
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2238_, v_____do__lift_2239_, v_____do__lift_2240_, v_____do__lift_2241_, v_____do__lift_2242_, v_x_2243_, v_toPure_2244_, v_inst_2245_, v___f_2246_, v_toBind_2247_, v_setNextMacroScope_2248_, v_inst_2249_, v_inst_2250_, v_inst_2251_, v_toMonadRef_2252_, v_inst_2253_, v_inst_2254_, v_toMonadExceptOf_2255_, v_getNextMacroScope_2256_, v_____do__lift_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2259_, lean_object* v_____do__lift_2260_, lean_object* v_____do__lift_2261_, lean_object* v_____do__lift_2262_, lean_object* v_x_2263_, lean_object* v_toPure_2264_, lean_object* v_inst_2265_, lean_object* v___f_2266_, lean_object* v_toBind_2267_, lean_object* v_setNextMacroScope_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_toMonadRef_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_toMonadExceptOf_2275_, lean_object* v_getNextMacroScope_2276_, lean_object* v_getMaxRecDepth_2277_, lean_object* v_____do__lift_2278_){
_start:
{
lean_object* v___f_2279_; lean_object* v___x_2280_; 
lean_inc(v_toBind_2267_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2279_, 0, v_methods_2259_);
lean_closure_set(v___f_2279_, 1, v_____do__lift_2260_);
lean_closure_set(v___f_2279_, 2, v_____do__lift_2261_);
lean_closure_set(v___f_2279_, 3, v_____do__lift_2278_);
lean_closure_set(v___f_2279_, 4, v_____do__lift_2262_);
lean_closure_set(v___f_2279_, 5, v_x_2263_);
lean_closure_set(v___f_2279_, 6, v_toPure_2264_);
lean_closure_set(v___f_2279_, 7, v_inst_2265_);
lean_closure_set(v___f_2279_, 8, v___f_2266_);
lean_closure_set(v___f_2279_, 9, v_toBind_2267_);
lean_closure_set(v___f_2279_, 10, v_setNextMacroScope_2268_);
lean_closure_set(v___f_2279_, 11, v_inst_2269_);
lean_closure_set(v___f_2279_, 12, v_inst_2270_);
lean_closure_set(v___f_2279_, 13, v_inst_2271_);
lean_closure_set(v___f_2279_, 14, v_toMonadRef_2272_);
lean_closure_set(v___f_2279_, 15, v_inst_2273_);
lean_closure_set(v___f_2279_, 16, v_inst_2274_);
lean_closure_set(v___f_2279_, 17, v_toMonadExceptOf_2275_);
lean_closure_set(v___f_2279_, 18, v_getNextMacroScope_2276_);
v___x_2280_ = lean_apply_4(v_toBind_2267_, lean_box(0), lean_box(0), v_getMaxRecDepth_2277_, v___f_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2281_ = _args[0];
lean_object* v_____do__lift_2282_ = _args[1];
lean_object* v_____do__lift_2283_ = _args[2];
lean_object* v_____do__lift_2284_ = _args[3];
lean_object* v_x_2285_ = _args[4];
lean_object* v_toPure_2286_ = _args[5];
lean_object* v_inst_2287_ = _args[6];
lean_object* v___f_2288_ = _args[7];
lean_object* v_toBind_2289_ = _args[8];
lean_object* v_setNextMacroScope_2290_ = _args[9];
lean_object* v_inst_2291_ = _args[10];
lean_object* v_inst_2292_ = _args[11];
lean_object* v_inst_2293_ = _args[12];
lean_object* v_toMonadRef_2294_ = _args[13];
lean_object* v_inst_2295_ = _args[14];
lean_object* v_inst_2296_ = _args[15];
lean_object* v_toMonadExceptOf_2297_ = _args[16];
lean_object* v_getNextMacroScope_2298_ = _args[17];
lean_object* v_getMaxRecDepth_2299_ = _args[18];
lean_object* v_____do__lift_2300_ = _args[19];
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2281_, v_____do__lift_2282_, v_____do__lift_2283_, v_____do__lift_2284_, v_x_2285_, v_toPure_2286_, v_inst_2287_, v___f_2288_, v_toBind_2289_, v_setNextMacroScope_2290_, v_inst_2291_, v_inst_2292_, v_inst_2293_, v_toMonadRef_2294_, v_inst_2295_, v_inst_2296_, v_toMonadExceptOf_2297_, v_getNextMacroScope_2298_, v_getMaxRecDepth_2299_, v_____do__lift_2300_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2302_, lean_object* v_methods_2303_, lean_object* v_____do__lift_2304_, lean_object* v_____do__lift_2305_, lean_object* v_x_2306_, lean_object* v_toPure_2307_, lean_object* v_inst_2308_, lean_object* v___f_2309_, lean_object* v_toBind_2310_, lean_object* v_setNextMacroScope_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_toMonadRef_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_toMonadExceptOf_2318_, lean_object* v_getNextMacroScope_2319_, lean_object* v_____do__lift_2320_){
_start:
{
lean_object* v_getRecDepth_2321_; lean_object* v_getMaxRecDepth_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
v_getRecDepth_2321_ = lean_ctor_get(v_inst_2302_, 1);
lean_inc(v_getRecDepth_2321_);
v_getMaxRecDepth_2322_ = lean_ctor_get(v_inst_2302_, 2);
lean_inc(v_getMaxRecDepth_2322_);
lean_dec_ref(v_inst_2302_);
lean_inc(v_toBind_2310_);
v___f_2323_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2323_, 0, v_methods_2303_);
lean_closure_set(v___f_2323_, 1, v_____do__lift_2320_);
lean_closure_set(v___f_2323_, 2, v_____do__lift_2304_);
lean_closure_set(v___f_2323_, 3, v_____do__lift_2305_);
lean_closure_set(v___f_2323_, 4, v_x_2306_);
lean_closure_set(v___f_2323_, 5, v_toPure_2307_);
lean_closure_set(v___f_2323_, 6, v_inst_2308_);
lean_closure_set(v___f_2323_, 7, v___f_2309_);
lean_closure_set(v___f_2323_, 8, v_toBind_2310_);
lean_closure_set(v___f_2323_, 9, v_setNextMacroScope_2311_);
lean_closure_set(v___f_2323_, 10, v_inst_2312_);
lean_closure_set(v___f_2323_, 11, v_inst_2313_);
lean_closure_set(v___f_2323_, 12, v_inst_2314_);
lean_closure_set(v___f_2323_, 13, v_toMonadRef_2315_);
lean_closure_set(v___f_2323_, 14, v_inst_2316_);
lean_closure_set(v___f_2323_, 15, v_inst_2317_);
lean_closure_set(v___f_2323_, 16, v_toMonadExceptOf_2318_);
lean_closure_set(v___f_2323_, 17, v_getNextMacroScope_2319_);
lean_closure_set(v___f_2323_, 18, v_getMaxRecDepth_2322_);
v___x_2324_ = lean_apply_4(v_toBind_2310_, lean_box(0), lean_box(0), v_getRecDepth_2321_, v___f_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2325_ = _args[0];
lean_object* v_methods_2326_ = _args[1];
lean_object* v_____do__lift_2327_ = _args[2];
lean_object* v_____do__lift_2328_ = _args[3];
lean_object* v_x_2329_ = _args[4];
lean_object* v_toPure_2330_ = _args[5];
lean_object* v_inst_2331_ = _args[6];
lean_object* v___f_2332_ = _args[7];
lean_object* v_toBind_2333_ = _args[8];
lean_object* v_setNextMacroScope_2334_ = _args[9];
lean_object* v_inst_2335_ = _args[10];
lean_object* v_inst_2336_ = _args[11];
lean_object* v_inst_2337_ = _args[12];
lean_object* v_toMonadRef_2338_ = _args[13];
lean_object* v_inst_2339_ = _args[14];
lean_object* v_inst_2340_ = _args[15];
lean_object* v_toMonadExceptOf_2341_ = _args[16];
lean_object* v_getNextMacroScope_2342_ = _args[17];
lean_object* v_____do__lift_2343_ = _args[18];
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2325_, v_methods_2326_, v_____do__lift_2327_, v_____do__lift_2328_, v_x_2329_, v_toPure_2330_, v_inst_2331_, v___f_2332_, v_toBind_2333_, v_setNextMacroScope_2334_, v_inst_2335_, v_inst_2336_, v_inst_2337_, v_toMonadRef_2338_, v_inst_2339_, v_inst_2340_, v_toMonadExceptOf_2341_, v_getNextMacroScope_2342_, v_____do__lift_2343_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2345_, lean_object* v_methods_2346_, lean_object* v_____do__lift_2347_, lean_object* v_x_2348_, lean_object* v_toPure_2349_, lean_object* v_inst_2350_, lean_object* v___f_2351_, lean_object* v_toBind_2352_, lean_object* v_setNextMacroScope_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_toMonadRef_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_toMonadExceptOf_2360_, lean_object* v_getNextMacroScope_2361_, lean_object* v_getContext_2362_, lean_object* v_____do__lift_2363_){
_start:
{
lean_object* v___f_2364_; lean_object* v___x_2365_; 
lean_inc(v_toBind_2352_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2364_, 0, v_inst_2345_);
lean_closure_set(v___f_2364_, 1, v_methods_2346_);
lean_closure_set(v___f_2364_, 2, v_____do__lift_2363_);
lean_closure_set(v___f_2364_, 3, v_____do__lift_2347_);
lean_closure_set(v___f_2364_, 4, v_x_2348_);
lean_closure_set(v___f_2364_, 5, v_toPure_2349_);
lean_closure_set(v___f_2364_, 6, v_inst_2350_);
lean_closure_set(v___f_2364_, 7, v___f_2351_);
lean_closure_set(v___f_2364_, 8, v_toBind_2352_);
lean_closure_set(v___f_2364_, 9, v_setNextMacroScope_2353_);
lean_closure_set(v___f_2364_, 10, v_inst_2354_);
lean_closure_set(v___f_2364_, 11, v_inst_2355_);
lean_closure_set(v___f_2364_, 12, v_inst_2356_);
lean_closure_set(v___f_2364_, 13, v_toMonadRef_2357_);
lean_closure_set(v___f_2364_, 14, v_inst_2358_);
lean_closure_set(v___f_2364_, 15, v_inst_2359_);
lean_closure_set(v___f_2364_, 16, v_toMonadExceptOf_2360_);
lean_closure_set(v___f_2364_, 17, v_getNextMacroScope_2361_);
v___x_2365_ = lean_apply_4(v_toBind_2352_, lean_box(0), lean_box(0), v_getContext_2362_, v___f_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2366_ = _args[0];
lean_object* v_methods_2367_ = _args[1];
lean_object* v_____do__lift_2368_ = _args[2];
lean_object* v_x_2369_ = _args[3];
lean_object* v_toPure_2370_ = _args[4];
lean_object* v_inst_2371_ = _args[5];
lean_object* v___f_2372_ = _args[6];
lean_object* v_toBind_2373_ = _args[7];
lean_object* v_setNextMacroScope_2374_ = _args[8];
lean_object* v_inst_2375_ = _args[9];
lean_object* v_inst_2376_ = _args[10];
lean_object* v_inst_2377_ = _args[11];
lean_object* v_toMonadRef_2378_ = _args[12];
lean_object* v_inst_2379_ = _args[13];
lean_object* v_inst_2380_ = _args[14];
lean_object* v_toMonadExceptOf_2381_ = _args[15];
lean_object* v_getNextMacroScope_2382_ = _args[16];
lean_object* v_getContext_2383_ = _args[17];
lean_object* v_____do__lift_2384_ = _args[18];
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2366_, v_methods_2367_, v_____do__lift_2368_, v_x_2369_, v_toPure_2370_, v_inst_2371_, v___f_2372_, v_toBind_2373_, v_setNextMacroScope_2374_, v_inst_2375_, v_inst_2376_, v_inst_2377_, v_toMonadRef_2378_, v_inst_2379_, v_inst_2380_, v_toMonadExceptOf_2381_, v_getNextMacroScope_2382_, v_getContext_2383_, v_____do__lift_2384_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2386_, lean_object* v_inst_2387_, lean_object* v_methods_2388_, lean_object* v_x_2389_, lean_object* v_toPure_2390_, lean_object* v_inst_2391_, lean_object* v___f_2392_, lean_object* v_toBind_2393_, lean_object* v_setNextMacroScope_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_toMonadRef_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_toMonadExceptOf_2401_, lean_object* v_getNextMacroScope_2402_, lean_object* v_____do__lift_2403_){
_start:
{
lean_object* v_getCurrMacroScope_2404_; lean_object* v_getContext_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; 
v_getCurrMacroScope_2404_ = lean_ctor_get(v_toMonadQuotation_2386_, 1);
lean_inc(v_getCurrMacroScope_2404_);
v_getContext_2405_ = lean_ctor_get(v_toMonadQuotation_2386_, 2);
lean_inc(v_getContext_2405_);
lean_dec_ref(v_toMonadQuotation_2386_);
lean_inc(v_toBind_2393_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2406_, 0, v_inst_2387_);
lean_closure_set(v___f_2406_, 1, v_methods_2388_);
lean_closure_set(v___f_2406_, 2, v_____do__lift_2403_);
lean_closure_set(v___f_2406_, 3, v_x_2389_);
lean_closure_set(v___f_2406_, 4, v_toPure_2390_);
lean_closure_set(v___f_2406_, 5, v_inst_2391_);
lean_closure_set(v___f_2406_, 6, v___f_2392_);
lean_closure_set(v___f_2406_, 7, v_toBind_2393_);
lean_closure_set(v___f_2406_, 8, v_setNextMacroScope_2394_);
lean_closure_set(v___f_2406_, 9, v_inst_2395_);
lean_closure_set(v___f_2406_, 10, v_inst_2396_);
lean_closure_set(v___f_2406_, 11, v_inst_2397_);
lean_closure_set(v___f_2406_, 12, v_toMonadRef_2398_);
lean_closure_set(v___f_2406_, 13, v_inst_2399_);
lean_closure_set(v___f_2406_, 14, v_inst_2400_);
lean_closure_set(v___f_2406_, 15, v_toMonadExceptOf_2401_);
lean_closure_set(v___f_2406_, 16, v_getNextMacroScope_2402_);
lean_closure_set(v___f_2406_, 17, v_getContext_2405_);
v___x_2407_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v_getCurrMacroScope_2404_, v___f_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2408_ = _args[0];
lean_object* v_inst_2409_ = _args[1];
lean_object* v_methods_2410_ = _args[2];
lean_object* v_x_2411_ = _args[3];
lean_object* v_toPure_2412_ = _args[4];
lean_object* v_inst_2413_ = _args[5];
lean_object* v___f_2414_ = _args[6];
lean_object* v_toBind_2415_ = _args[7];
lean_object* v_setNextMacroScope_2416_ = _args[8];
lean_object* v_inst_2417_ = _args[9];
lean_object* v_inst_2418_ = _args[10];
lean_object* v_inst_2419_ = _args[11];
lean_object* v_toMonadRef_2420_ = _args[12];
lean_object* v_inst_2421_ = _args[13];
lean_object* v_inst_2422_ = _args[14];
lean_object* v_toMonadExceptOf_2423_ = _args[15];
lean_object* v_getNextMacroScope_2424_ = _args[16];
lean_object* v_____do__lift_2425_ = _args[17];
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2408_, v_inst_2409_, v_methods_2410_, v_x_2411_, v_toPure_2412_, v_inst_2413_, v___f_2414_, v_toBind_2415_, v_setNextMacroScope_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_toMonadRef_2420_, v_inst_2421_, v_inst_2422_, v_toMonadExceptOf_2423_, v_getNextMacroScope_2424_, v_____do__lift_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2427_, lean_object* v_env_2428_, lean_object* v_currNamespace_2429_, lean_object* v_opts_2430_, lean_object* v___x_2431_, lean_object* v___f_2432_, lean_object* v___f_2433_, lean_object* v_toMonadQuotation_2434_, lean_object* v_inst_2435_, lean_object* v_x_2436_, lean_object* v_toPure_2437_, lean_object* v_inst_2438_, lean_object* v___f_2439_, lean_object* v_toBind_2440_, lean_object* v_setNextMacroScope_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_toMonadExceptOf_2447_, lean_object* v_getNextMacroScope_2448_, lean_object* v_openDecls_2449_){
_start:
{
lean_object* v_getRef_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v_methods_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; 
v_getRef_2450_ = lean_ctor_get(v_toMonadRef_2427_, 0);
lean_inc(v_getRef_2450_);
lean_inc(v_openDecls_2449_);
lean_inc_n(v_currNamespace_2429_, 2);
lean_inc_ref(v_env_2428_);
v___f_2451_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2451_, 0, v_env_2428_);
lean_closure_set(v___f_2451_, 1, v_currNamespace_2429_);
lean_closure_set(v___f_2451_, 2, v_openDecls_2449_);
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2452_, 0, v_env_2428_);
lean_closure_set(v___f_2452_, 1, v_opts_2430_);
lean_closure_set(v___f_2452_, 2, v_currNamespace_2429_);
lean_closure_set(v___f_2452_, 3, v_openDecls_2449_);
v___x_2453_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2453_, 0, lean_box(0));
lean_closure_set(v___x_2453_, 1, lean_box(0));
lean_closure_set(v___x_2453_, 2, v___x_2431_);
lean_closure_set(v___x_2453_, 3, lean_box(0));
lean_closure_set(v___x_2453_, 4, v_currNamespace_2429_);
v_methods_2454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2454_, 0, v___f_2432_);
lean_ctor_set(v_methods_2454_, 1, v___x_2453_);
lean_ctor_set(v_methods_2454_, 2, v___f_2433_);
lean_ctor_set(v_methods_2454_, 3, v___f_2451_);
lean_ctor_set(v_methods_2454_, 4, v___f_2452_);
lean_inc(v_toBind_2440_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2455_, 0, v_toMonadQuotation_2434_);
lean_closure_set(v___f_2455_, 1, v_inst_2435_);
lean_closure_set(v___f_2455_, 2, v_methods_2454_);
lean_closure_set(v___f_2455_, 3, v_x_2436_);
lean_closure_set(v___f_2455_, 4, v_toPure_2437_);
lean_closure_set(v___f_2455_, 5, v_inst_2438_);
lean_closure_set(v___f_2455_, 6, v___f_2439_);
lean_closure_set(v___f_2455_, 7, v_toBind_2440_);
lean_closure_set(v___f_2455_, 8, v_setNextMacroScope_2441_);
lean_closure_set(v___f_2455_, 9, v_inst_2442_);
lean_closure_set(v___f_2455_, 10, v_inst_2443_);
lean_closure_set(v___f_2455_, 11, v_inst_2444_);
lean_closure_set(v___f_2455_, 12, v_toMonadRef_2427_);
lean_closure_set(v___f_2455_, 13, v_inst_2445_);
lean_closure_set(v___f_2455_, 14, v_inst_2446_);
lean_closure_set(v___f_2455_, 15, v_toMonadExceptOf_2447_);
lean_closure_set(v___f_2455_, 16, v_getNextMacroScope_2448_);
v___x_2456_ = lean_apply_4(v_toBind_2440_, lean_box(0), lean_box(0), v_getRef_2450_, v___f_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2457_ = _args[0];
lean_object* v_env_2458_ = _args[1];
lean_object* v_currNamespace_2459_ = _args[2];
lean_object* v_opts_2460_ = _args[3];
lean_object* v___x_2461_ = _args[4];
lean_object* v___f_2462_ = _args[5];
lean_object* v___f_2463_ = _args[6];
lean_object* v_toMonadQuotation_2464_ = _args[7];
lean_object* v_inst_2465_ = _args[8];
lean_object* v_x_2466_ = _args[9];
lean_object* v_toPure_2467_ = _args[10];
lean_object* v_inst_2468_ = _args[11];
lean_object* v___f_2469_ = _args[12];
lean_object* v_toBind_2470_ = _args[13];
lean_object* v_setNextMacroScope_2471_ = _args[14];
lean_object* v_inst_2472_ = _args[15];
lean_object* v_inst_2473_ = _args[16];
lean_object* v_inst_2474_ = _args[17];
lean_object* v_inst_2475_ = _args[18];
lean_object* v_inst_2476_ = _args[19];
lean_object* v_toMonadExceptOf_2477_ = _args[20];
lean_object* v_getNextMacroScope_2478_ = _args[21];
lean_object* v_openDecls_2479_ = _args[22];
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2457_, v_env_2458_, v_currNamespace_2459_, v_opts_2460_, v___x_2461_, v___f_2462_, v___f_2463_, v_toMonadQuotation_2464_, v_inst_2465_, v_x_2466_, v_toPure_2467_, v_inst_2468_, v___f_2469_, v_toBind_2470_, v_setNextMacroScope_2471_, v_inst_2472_, v_inst_2473_, v_inst_2474_, v_inst_2475_, v_inst_2476_, v_toMonadExceptOf_2477_, v_getNextMacroScope_2478_, v_openDecls_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2481_, lean_object* v_env_2482_, lean_object* v_opts_2483_, lean_object* v___x_2484_, lean_object* v___f_2485_, lean_object* v___f_2486_, lean_object* v_toMonadQuotation_2487_, lean_object* v_inst_2488_, lean_object* v_x_2489_, lean_object* v_toPure_2490_, lean_object* v_inst_2491_, lean_object* v___f_2492_, lean_object* v_toBind_2493_, lean_object* v_setNextMacroScope_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_toMonadExceptOf_2500_, lean_object* v_getNextMacroScope_2501_, lean_object* v_getOpenDecls_2502_, lean_object* v_currNamespace_2503_){
_start:
{
lean_object* v___f_2504_; lean_object* v___x_2505_; 
lean_inc(v_toBind_2493_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2504_, 0, v_toMonadRef_2481_);
lean_closure_set(v___f_2504_, 1, v_env_2482_);
lean_closure_set(v___f_2504_, 2, v_currNamespace_2503_);
lean_closure_set(v___f_2504_, 3, v_opts_2483_);
lean_closure_set(v___f_2504_, 4, v___x_2484_);
lean_closure_set(v___f_2504_, 5, v___f_2485_);
lean_closure_set(v___f_2504_, 6, v___f_2486_);
lean_closure_set(v___f_2504_, 7, v_toMonadQuotation_2487_);
lean_closure_set(v___f_2504_, 8, v_inst_2488_);
lean_closure_set(v___f_2504_, 9, v_x_2489_);
lean_closure_set(v___f_2504_, 10, v_toPure_2490_);
lean_closure_set(v___f_2504_, 11, v_inst_2491_);
lean_closure_set(v___f_2504_, 12, v___f_2492_);
lean_closure_set(v___f_2504_, 13, v_toBind_2493_);
lean_closure_set(v___f_2504_, 14, v_setNextMacroScope_2494_);
lean_closure_set(v___f_2504_, 15, v_inst_2495_);
lean_closure_set(v___f_2504_, 16, v_inst_2496_);
lean_closure_set(v___f_2504_, 17, v_inst_2497_);
lean_closure_set(v___f_2504_, 18, v_inst_2498_);
lean_closure_set(v___f_2504_, 19, v_inst_2499_);
lean_closure_set(v___f_2504_, 20, v_toMonadExceptOf_2500_);
lean_closure_set(v___f_2504_, 21, v_getNextMacroScope_2501_);
v___x_2505_ = lean_apply_4(v_toBind_2493_, lean_box(0), lean_box(0), v_getOpenDecls_2502_, v___f_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2506_ = _args[0];
lean_object* v_env_2507_ = _args[1];
lean_object* v_opts_2508_ = _args[2];
lean_object* v___x_2509_ = _args[3];
lean_object* v___f_2510_ = _args[4];
lean_object* v___f_2511_ = _args[5];
lean_object* v_toMonadQuotation_2512_ = _args[6];
lean_object* v_inst_2513_ = _args[7];
lean_object* v_x_2514_ = _args[8];
lean_object* v_toPure_2515_ = _args[9];
lean_object* v_inst_2516_ = _args[10];
lean_object* v___f_2517_ = _args[11];
lean_object* v_toBind_2518_ = _args[12];
lean_object* v_setNextMacroScope_2519_ = _args[13];
lean_object* v_inst_2520_ = _args[14];
lean_object* v_inst_2521_ = _args[15];
lean_object* v_inst_2522_ = _args[16];
lean_object* v_inst_2523_ = _args[17];
lean_object* v_inst_2524_ = _args[18];
lean_object* v_toMonadExceptOf_2525_ = _args[19];
lean_object* v_getNextMacroScope_2526_ = _args[20];
lean_object* v_getOpenDecls_2527_ = _args[21];
lean_object* v_currNamespace_2528_ = _args[22];
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2506_, v_env_2507_, v_opts_2508_, v___x_2509_, v___f_2510_, v___f_2511_, v_toMonadQuotation_2512_, v_inst_2513_, v_x_2514_, v_toPure_2515_, v_inst_2516_, v___f_2517_, v_toBind_2518_, v_setNextMacroScope_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_, v_inst_2523_, v_inst_2524_, v_toMonadExceptOf_2525_, v_getNextMacroScope_2526_, v_getOpenDecls_2527_, v_currNamespace_2528_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2530_, lean_object* v_toMonadRef_2531_, lean_object* v_env_2532_, lean_object* v___x_2533_, lean_object* v___f_2534_, lean_object* v___f_2535_, lean_object* v_toMonadQuotation_2536_, lean_object* v_inst_2537_, lean_object* v_x_2538_, lean_object* v_toPure_2539_, lean_object* v_inst_2540_, lean_object* v___f_2541_, lean_object* v_toBind_2542_, lean_object* v_setNextMacroScope_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_toMonadExceptOf_2549_, lean_object* v_getNextMacroScope_2550_, lean_object* v_opts_2551_){
_start:
{
lean_object* v_getCurrNamespace_2552_; lean_object* v_getOpenDecls_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
v_getCurrNamespace_2552_ = lean_ctor_get(v_inst_2530_, 0);
lean_inc(v_getCurrNamespace_2552_);
v_getOpenDecls_2553_ = lean_ctor_get(v_inst_2530_, 1);
lean_inc(v_getOpenDecls_2553_);
lean_dec_ref(v_inst_2530_);
lean_inc(v_toBind_2542_);
v___f_2554_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2554_, 0, v_toMonadRef_2531_);
lean_closure_set(v___f_2554_, 1, v_env_2532_);
lean_closure_set(v___f_2554_, 2, v_opts_2551_);
lean_closure_set(v___f_2554_, 3, v___x_2533_);
lean_closure_set(v___f_2554_, 4, v___f_2534_);
lean_closure_set(v___f_2554_, 5, v___f_2535_);
lean_closure_set(v___f_2554_, 6, v_toMonadQuotation_2536_);
lean_closure_set(v___f_2554_, 7, v_inst_2537_);
lean_closure_set(v___f_2554_, 8, v_x_2538_);
lean_closure_set(v___f_2554_, 9, v_toPure_2539_);
lean_closure_set(v___f_2554_, 10, v_inst_2540_);
lean_closure_set(v___f_2554_, 11, v___f_2541_);
lean_closure_set(v___f_2554_, 12, v_toBind_2542_);
lean_closure_set(v___f_2554_, 13, v_setNextMacroScope_2543_);
lean_closure_set(v___f_2554_, 14, v_inst_2544_);
lean_closure_set(v___f_2554_, 15, v_inst_2545_);
lean_closure_set(v___f_2554_, 16, v_inst_2546_);
lean_closure_set(v___f_2554_, 17, v_inst_2547_);
lean_closure_set(v___f_2554_, 18, v_inst_2548_);
lean_closure_set(v___f_2554_, 19, v_toMonadExceptOf_2549_);
lean_closure_set(v___f_2554_, 20, v_getNextMacroScope_2550_);
lean_closure_set(v___f_2554_, 21, v_getOpenDecls_2553_);
v___x_2555_ = lean_apply_4(v_toBind_2542_, lean_box(0), lean_box(0), v_getCurrNamespace_2552_, v___f_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2556_ = _args[0];
lean_object* v_toMonadRef_2557_ = _args[1];
lean_object* v_env_2558_ = _args[2];
lean_object* v___x_2559_ = _args[3];
lean_object* v___f_2560_ = _args[4];
lean_object* v___f_2561_ = _args[5];
lean_object* v_toMonadQuotation_2562_ = _args[6];
lean_object* v_inst_2563_ = _args[7];
lean_object* v_x_2564_ = _args[8];
lean_object* v_toPure_2565_ = _args[9];
lean_object* v_inst_2566_ = _args[10];
lean_object* v___f_2567_ = _args[11];
lean_object* v_toBind_2568_ = _args[12];
lean_object* v_setNextMacroScope_2569_ = _args[13];
lean_object* v_inst_2570_ = _args[14];
lean_object* v_inst_2571_ = _args[15];
lean_object* v_inst_2572_ = _args[16];
lean_object* v_inst_2573_ = _args[17];
lean_object* v_inst_2574_ = _args[18];
lean_object* v_toMonadExceptOf_2575_ = _args[19];
lean_object* v_getNextMacroScope_2576_ = _args[20];
lean_object* v_opts_2577_ = _args[21];
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2556_, v_toMonadRef_2557_, v_env_2558_, v___x_2559_, v___f_2560_, v___f_2561_, v_toMonadQuotation_2562_, v_inst_2563_, v_x_2564_, v_toPure_2565_, v_inst_2566_, v___f_2567_, v_toBind_2568_, v_setNextMacroScope_2569_, v_inst_2570_, v_inst_2571_, v_inst_2572_, v_inst_2573_, v_inst_2574_, v_toMonadExceptOf_2575_, v_getNextMacroScope_2576_, v_opts_2577_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v___x_2579_, lean_object* v___x_2580_, lean_object* v_inst_2581_, lean_object* v_toMonadRef_2582_, lean_object* v___x_2583_, lean_object* v_toMonadQuotation_2584_, lean_object* v_inst_2585_, lean_object* v_x_2586_, lean_object* v_toPure_2587_, lean_object* v_inst_2588_, lean_object* v___f_2589_, lean_object* v_toBind_2590_, lean_object* v_setNextMacroScope_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_toMonadExceptOf_2597_, lean_object* v_getNextMacroScope_2598_, lean_object* v_env_2599_){
_start:
{
lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; 
lean_inc_ref_n(v_env_2599_, 2);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2600_, 0, v_env_2599_);
lean_closure_set(v___f_2600_, 1, v___x_2579_);
lean_closure_set(v___f_2600_, 2, v___x_2580_);
v___f_2601_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2601_, 0, v_env_2599_);
lean_inc(v_inst_2594_);
lean_inc(v_toBind_2590_);
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2602_, 0, v_inst_2581_);
lean_closure_set(v___f_2602_, 1, v_toMonadRef_2582_);
lean_closure_set(v___f_2602_, 2, v_env_2599_);
lean_closure_set(v___f_2602_, 3, v___x_2583_);
lean_closure_set(v___f_2602_, 4, v___f_2600_);
lean_closure_set(v___f_2602_, 5, v___f_2601_);
lean_closure_set(v___f_2602_, 6, v_toMonadQuotation_2584_);
lean_closure_set(v___f_2602_, 7, v_inst_2585_);
lean_closure_set(v___f_2602_, 8, v_x_2586_);
lean_closure_set(v___f_2602_, 9, v_toPure_2587_);
lean_closure_set(v___f_2602_, 10, v_inst_2588_);
lean_closure_set(v___f_2602_, 11, v___f_2589_);
lean_closure_set(v___f_2602_, 12, v_toBind_2590_);
lean_closure_set(v___f_2602_, 13, v_setNextMacroScope_2591_);
lean_closure_set(v___f_2602_, 14, v_inst_2592_);
lean_closure_set(v___f_2602_, 15, v_inst_2593_);
lean_closure_set(v___f_2602_, 16, v_inst_2594_);
lean_closure_set(v___f_2602_, 17, v_inst_2595_);
lean_closure_set(v___f_2602_, 18, v_inst_2596_);
lean_closure_set(v___f_2602_, 19, v_toMonadExceptOf_2597_);
lean_closure_set(v___f_2602_, 20, v_getNextMacroScope_2598_);
v___x_2603_ = lean_apply_4(v_toBind_2590_, lean_box(0), lean_box(0), v_inst_2594_, v___f_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_2604_ = _args[0];
lean_object* v___x_2605_ = _args[1];
lean_object* v_inst_2606_ = _args[2];
lean_object* v_toMonadRef_2607_ = _args[3];
lean_object* v___x_2608_ = _args[4];
lean_object* v_toMonadQuotation_2609_ = _args[5];
lean_object* v_inst_2610_ = _args[6];
lean_object* v_x_2611_ = _args[7];
lean_object* v_toPure_2612_ = _args[8];
lean_object* v_inst_2613_ = _args[9];
lean_object* v___f_2614_ = _args[10];
lean_object* v_toBind_2615_ = _args[11];
lean_object* v_setNextMacroScope_2616_ = _args[12];
lean_object* v_inst_2617_ = _args[13];
lean_object* v_inst_2618_ = _args[14];
lean_object* v_inst_2619_ = _args[15];
lean_object* v_inst_2620_ = _args[16];
lean_object* v_inst_2621_ = _args[17];
lean_object* v_toMonadExceptOf_2622_ = _args[18];
lean_object* v_getNextMacroScope_2623_ = _args[19];
lean_object* v_env_2624_ = _args[20];
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v___x_2604_, v___x_2605_, v_inst_2606_, v_toMonadRef_2607_, v___x_2608_, v_toMonadQuotation_2609_, v_inst_2610_, v_x_2611_, v_toPure_2612_, v_inst_2613_, v___f_2614_, v_toBind_2615_, v_setNextMacroScope_2616_, v_inst_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_toMonadExceptOf_2622_, v_getNextMacroScope_2623_, v_env_2624_);
return v_res_2625_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_EStateM_nonBacktrackable(lean_box(0));
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2647_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2646_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___f_2649_; 
v___x_2648_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2649_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2649_, 0, v___x_2648_);
return v___f_2649_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___f_2651_; 
v___x_2650_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2651_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2651_, 0, v___x_2650_);
return v___f_2651_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; 
v___f_2652_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2653_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___f_2653_);
lean_ctor_set(v___x_2654_, 1, v___f_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_toApplicative_2669_; lean_object* v_toBind_2670_; lean_object* v_getEnv_2671_; lean_object* v_toMonadExceptOf_2672_; lean_object* v_toMonadRef_2673_; lean_object* v_toMonadQuotation_2674_; lean_object* v_getNextMacroScope_2675_; lean_object* v_setNextMacroScope_2676_; lean_object* v_toPure_2677_; lean_object* v___x_2678_; lean_object* v___f_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; 
v___x_2667_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2668_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2669_ = lean_ctor_get(v_inst_2657_, 0);
v_toBind_2670_ = lean_ctor_get(v_inst_2657_, 1);
lean_inc_n(v_toBind_2670_, 3);
v_getEnv_2671_ = lean_ctor_get(v_inst_2659_, 0);
lean_inc(v_getEnv_2671_);
v_toMonadExceptOf_2672_ = lean_ctor_get(v_inst_2661_, 0);
lean_inc_ref(v_toMonadExceptOf_2672_);
v_toMonadRef_2673_ = lean_ctor_get(v_inst_2661_, 1);
lean_inc_ref_n(v_toMonadRef_2673_, 2);
v_toMonadQuotation_2674_ = lean_ctor_get(v_inst_2658_, 0);
lean_inc_ref(v_toMonadQuotation_2674_);
v_getNextMacroScope_2675_ = lean_ctor_get(v_inst_2658_, 1);
lean_inc(v_getNextMacroScope_2675_);
v_setNextMacroScope_2676_ = lean_ctor_get(v_inst_2658_, 2);
lean_inc(v_setNextMacroScope_2676_);
lean_dec_ref(v_inst_2658_);
v_toPure_2677_ = lean_ctor_get(v_toApplicative_2669_, 1);
lean_inc_n(v_toPure_2677_, 2);
v___x_2678_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2664_);
lean_inc(v_inst_2665_);
lean_inc_ref(v_inst_2657_);
lean_inc_ref(v_inst_2663_);
v___f_2679_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2679_, 0, v_inst_2663_);
lean_closure_set(v___f_2679_, 1, v_toPure_2677_);
lean_closure_set(v___f_2679_, 2, v_inst_2657_);
lean_closure_set(v___f_2679_, 3, v_toMonadRef_2673_);
lean_closure_set(v___f_2679_, 4, v_inst_2665_);
lean_closure_set(v___f_2679_, 5, v_toBind_2670_);
lean_closure_set(v___f_2679_, 6, v_inst_2664_);
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2680_, 0, v___x_2668_);
lean_closure_set(v___f_2680_, 1, v___x_2678_);
lean_closure_set(v___f_2680_, 2, v_inst_2662_);
lean_closure_set(v___f_2680_, 3, v_toMonadRef_2673_);
lean_closure_set(v___f_2680_, 4, v___x_2667_);
lean_closure_set(v___f_2680_, 5, v_toMonadQuotation_2674_);
lean_closure_set(v___f_2680_, 6, v_inst_2660_);
lean_closure_set(v___f_2680_, 7, v_x_2666_);
lean_closure_set(v___f_2680_, 8, v_toPure_2677_);
lean_closure_set(v___f_2680_, 9, v_inst_2657_);
lean_closure_set(v___f_2680_, 10, v___f_2679_);
lean_closure_set(v___f_2680_, 11, v_toBind_2670_);
lean_closure_set(v___f_2680_, 12, v_setNextMacroScope_2676_);
lean_closure_set(v___f_2680_, 13, v_inst_2659_);
lean_closure_set(v___f_2680_, 14, v_inst_2663_);
lean_closure_set(v___f_2680_, 15, v_inst_2664_);
lean_closure_set(v___f_2680_, 16, v_inst_2665_);
lean_closure_set(v___f_2680_, 17, v_inst_2661_);
lean_closure_set(v___f_2680_, 18, v_toMonadExceptOf_2672_);
lean_closure_set(v___f_2680_, 19, v_getNextMacroScope_2675_);
v___x_2681_ = lean_apply_4(v_toBind_2670_, lean_box(0), lean_box(0), v_getEnv_2671_, v___f_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2682_, lean_object* v_00_u03b1_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2684_, v_inst_2685_, v_inst_2686_, v_inst_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2696_, lean_object* v_00_u03b1_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_x_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Elab_liftMacroM(v_m_2696_, v_00_u03b1_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_x_2708_);
lean_dec(v_inst_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_x_2719_, lean_object* v_stx_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_apply_1(v_x_2719_, v_stx_2720_);
v___x_2722_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_inst_2713_, v_inst_2714_, v_inst_2715_, v_inst_2716_, v_inst_2717_, v_inst_2718_, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_x_2734_, lean_object* v_stx_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_apply_1(v_x_2734_, v_stx_2735_);
v___x_2737_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2724_, v_inst_2725_, v_inst_2726_, v_inst_2727_, v_inst_2728_, v_inst_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_x_2749_, lean_object* v_stx_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Elab_adaptMacro(v_m_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_inst_2744_, v_inst_2745_, v_inst_2746_, v_inst_2747_, v_inst_2748_, v_x_2749_, v_stx_2750_);
lean_dec(v_inst_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2752_, lean_object* v_currNamespace_2753_, lean_object* v_idx_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_name_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_inc(v_idx_2754_);
lean_inc(v_baseName_2752_);
v_name_2757_ = lean_name_append_index_after(v_baseName_2752_, v_idx_2754_);
lean_inc(v_name_2757_);
lean_inc(v_currNamespace_2753_);
v___x_2758_ = l_Lean_Name_append(v_currNamespace_2753_, v_name_2757_);
v___x_2759_ = l_Lean_Macro_hasDecl(v___x_2758_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; uint8_t v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
v___x_2761_ = lean_unbox(v_a_2760_);
lean_dec(v_a_2760_);
if (v___x_2761_ == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_idx_2754_);
lean_dec(v_currNamespace_2753_);
lean_dec(v_baseName_2752_);
v_a_2762_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2759_, 0);
lean_dec(v_unused_2770_);
v___x_2764_ = v___x_2759_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2759_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_name_2757_);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_name_2757_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v_name_2757_);
v_a_2771_ = lean_ctor_get(v___x_2759_, 1);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2759_);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_nat_add(v_idx_2754_, v___x_2772_);
lean_dec(v_idx_2754_);
v_idx_2754_ = v___x_2773_;
v_a_2756_ = v_a_2771_;
goto _start;
}
}
else
{
lean_object* v_a_2775_; lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_name_2757_);
lean_dec(v_idx_2754_);
lean_dec(v_currNamespace_2753_);
lean_dec(v_baseName_2752_);
v_a_2775_ = lean_ctor_get(v___x_2759_, 0);
v_a_2776_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2759_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_inc(v_a_2775_);
lean_dec(v___x_2759_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2775_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2784_, lean_object* v_currNamespace_2785_, lean_object* v_idx_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2784_, v_currNamespace_2785_, v_idx_2786_, v_a_2787_, v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Macro_getCurrNamespace(v_a_2791_, v_a_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_n(v_a_2794_, 2);
v_a_2795_ = lean_ctor_get(v___x_2793_, 1);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2793_);
lean_inc(v_baseName_2790_);
v___x_2796_ = l_Lean_Name_append(v_a_2794_, v_baseName_2790_);
v___x_2797_ = l_Lean_Macro_hasDecl(v___x_2796_, v_a_2791_, v_a_2795_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
v___x_2799_ = lean_unbox(v_a_2798_);
lean_dec(v_a_2798_);
if (v___x_2799_ == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2794_);
v_a_2800_ = lean_ctor_get(v___x_2797_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2797_, 0);
lean_dec(v_unused_2808_);
v___x_2802_ = v___x_2797_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2797_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_baseName_2790_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_baseName_2790_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2797_, 1);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2797_);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2790_, v_a_2794_, v___x_2810_, v_a_2791_, v_a_2809_);
return v___x_2811_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2794_);
lean_dec(v_baseName_2790_);
v_a_2812_ = lean_ctor_get(v___x_2797_, 0);
v_a_2813_ = lean_ctor_get(v___x_2797_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2797_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_inc(v_a_2812_);
lean_dec(v___x_2797_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_dec(v_baseName_2790_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2821_, v_a_2822_, v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2824_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_name_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2833_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2834_ = l_Lean_MessageData_ofName(v_name_2832_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_logError___redArg(v_inst_2828_, v_inst_2829_, v_inst_2830_, v_inst_2831_, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_inst_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_ex_2842_){
_start:
{
if (lean_obj_tag(v_ex_2842_) == 0)
{
lean_object* v_ref_2843_; lean_object* v_msg_2844_; lean_object* v___x_2845_; 
lean_dec(v_inst_2841_);
v_ref_2843_ = lean_ctor_get(v_ex_2842_, 0);
lean_inc(v_ref_2843_);
v_msg_2844_ = lean_ctor_get(v_ex_2842_, 1);
lean_inc_ref(v_msg_2844_);
lean_dec_ref(v_ex_2842_);
v___x_2845_ = l_Lean_logErrorAt___redArg(v_inst_2837_, v_inst_2838_, v_inst_2839_, v_inst_2840_, v_ref_2843_, v_msg_2844_);
return v___x_2845_;
}
else
{
lean_object* v_id_2846_; lean_object* v___f_2847_; uint8_t v___y_2849_; uint8_t v___x_2858_; 
v_id_2846_ = lean_ctor_get(v_ex_2842_, 0);
lean_inc(v_id_2846_);
lean_inc_ref(v_inst_2837_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2847_, 0, v_inst_2837_);
lean_closure_set(v___f_2847_, 1, v_inst_2838_);
lean_closure_set(v___f_2847_, 2, v_inst_2839_);
lean_closure_set(v___f_2847_, 3, v_inst_2840_);
v___x_2858_ = l_Lean_Elab_isAbortExceptionId(v_id_2846_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
v___x_2859_ = l_Lean_Exception_isInterrupt(v_ex_2842_);
lean_dec_ref(v_ex_2842_);
v___y_2849_ = v___x_2859_;
goto v___jp_2848_;
}
else
{
lean_dec_ref(v_ex_2842_);
v___y_2849_ = v___x_2858_;
goto v___jp_2848_;
}
v___jp_2848_:
{
if (v___y_2849_ == 0)
{
lean_object* v_toBind_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_toBind_2850_ = lean_ctor_get(v_inst_2837_, 1);
lean_inc(v_toBind_2850_);
lean_dec_ref(v_inst_2837_);
v___x_2851_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2851_, 0, v_id_2846_);
v___x_2852_ = lean_apply_2(v_inst_2841_, lean_box(0), v___x_2851_);
v___x_2853_ = lean_apply_4(v_toBind_2850_, lean_box(0), lean_box(0), v___x_2852_, v___f_2847_);
return v___x_2853_;
}
else
{
lean_object* v_toApplicative_2854_; lean_object* v_toPure_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec_ref(v___f_2847_);
lean_dec(v_id_2846_);
lean_dec(v_inst_2841_);
v_toApplicative_2854_ = lean_ctor_get(v_inst_2837_, 0);
lean_inc_ref(v_toApplicative_2854_);
lean_dec_ref(v_inst_2837_);
v_toPure_2855_ = lean_ctor_get(v_toApplicative_2854_, 1);
lean_inc(v_toPure_2855_);
lean_dec_ref(v_toApplicative_2854_);
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_apply_2(v_toPure_2855_, lean_box(0), v___x_2856_);
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_ex_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_Elab_logException___redArg(v_inst_2861_, v_inst_2862_, v_inst_2863_, v_inst_2864_, v_inst_2865_, v_ex_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_ex_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Elab_logException___redArg(v_inst_2868_, v_inst_2869_, v_inst_2870_, v_inst_2871_, v_inst_2872_, v_ex_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_x_2881_){
_start:
{
lean_object* v_tryCatch_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; 
v_tryCatch_2882_ = lean_ctor_get(v_inst_2877_, 1);
lean_inc(v_tryCatch_2882_);
lean_dec_ref(v_inst_2877_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2883_, 0, v_inst_2875_);
lean_closure_set(v___f_2883_, 1, v_inst_2876_);
lean_closure_set(v___f_2883_, 2, v_inst_2878_);
lean_closure_set(v___f_2883_, 3, v_inst_2879_);
lean_closure_set(v___f_2883_, 4, v_inst_2880_);
v___x_2884_ = lean_apply_3(v_tryCatch_2882_, lean_box(0), v_x_2881_, v___f_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2885_, lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Elab_withLogging___redArg(v_inst_2886_, v_inst_2887_, v_inst_2888_, v_inst_2889_, v_inst_2890_, v_inst_2891_, v_x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2897_, lean_object* v_ex_2898_, lean_object* v_toPure_2899_, lean_object* v_____do__lift_2900_){
_start:
{
lean_object* v_exPosition_2901_; lean_object* v_line_2902_; lean_object* v_column_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2923_; 
v_exPosition_2901_ = l_Lean_FileMap_toPosition(v_____do__lift_2900_, v_val_2897_);
v_line_2902_ = lean_ctor_get(v_exPosition_2901_, 0);
v_column_2903_ = lean_ctor_get(v_exPosition_2901_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_exPosition_2901_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2905_ = v_exPosition_2901_;
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_column_2903_);
lean_inc(v_line_2902_);
lean_dec(v_exPosition_2901_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2907_ = l_Nat_reprFast(v_line_2902_);
v___x_2908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
v___x_2909_ = l_Lean_MessageData_ofFormat(v___x_2908_);
v___x_2910_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 7);
lean_ctor_set(v___x_2905_, 1, v___x_2910_);
lean_ctor_set(v___x_2905_, 0, v___x_2909_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2913_ = l_Nat_reprFast(v_column_2903_);
v___x_2914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
v___x_2915_ = l_Lean_MessageData_ofFormat(v___x_2914_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2912_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_Exception_toMessageData(v_ex_2898_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_apply_2(v_toPure_2899_, lean_box(0), v___x_2920_);
return v___x_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2924_, lean_object* v_ex_2925_, lean_object* v_toPure_2926_, lean_object* v_____do__lift_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2924_, v_ex_2925_, v_toPure_2926_, v_____do__lift_2927_);
lean_dec(v_val_2924_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2929_, lean_object* v_toPure_2930_, lean_object* v_inst_2931_, lean_object* v_toBind_2932_, lean_object* v_pos_2933_){
_start:
{
lean_object* v___x_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = l_Lean_Exception_getRef(v_ex_2929_);
v___x_2935_ = 0;
v___x_2936_ = l_Lean_Syntax_getPos_x3f(v___x_2934_, v___x_2935_);
lean_dec(v___x_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec(v_toBind_2932_);
lean_dec_ref(v_inst_2931_);
v___x_2937_ = l_Lean_Exception_toMessageData(v_ex_2929_);
v___x_2938_ = lean_apply_2(v_toPure_2930_, lean_box(0), v___x_2937_);
return v___x_2938_;
}
else
{
lean_object* v_val_2939_; uint8_t v___x_2940_; 
v_val_2939_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_val_2939_);
lean_dec_ref(v___x_2936_);
v___x_2940_ = lean_nat_dec_eq(v_pos_2933_, v_val_2939_);
if (v___x_2940_ == 0)
{
lean_object* v_toMonadFileMap_2941_; lean_object* v___f_2942_; lean_object* v___x_2943_; 
v_toMonadFileMap_2941_ = lean_ctor_get(v_inst_2931_, 0);
lean_inc(v_toMonadFileMap_2941_);
lean_dec_ref(v_inst_2931_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2942_, 0, v_val_2939_);
lean_closure_set(v___f_2942_, 1, v_ex_2929_);
lean_closure_set(v___f_2942_, 2, v_toPure_2930_);
v___x_2943_ = lean_apply_4(v_toBind_2932_, lean_box(0), lean_box(0), v_toMonadFileMap_2941_, v___f_2942_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v_val_2939_);
lean_dec(v_toBind_2932_);
lean_dec_ref(v_inst_2931_);
v___x_2944_ = l_Lean_Exception_toMessageData(v_ex_2929_);
v___x_2945_ = lean_apply_2(v_toPure_2930_, lean_box(0), v___x_2944_);
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2946_, lean_object* v_toPure_2947_, lean_object* v_inst_2948_, lean_object* v_toBind_2949_, lean_object* v_pos_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2946_, v_toPure_2947_, v_inst_2948_, v_toBind_2949_, v_pos_2950_);
lean_dec(v_pos_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_ex_2954_){
_start:
{
lean_object* v_toApplicative_2955_; lean_object* v_toBind_2956_; lean_object* v_toPure_2957_; lean_object* v___x_2958_; lean_object* v___f_2959_; lean_object* v___x_2960_; 
v_toApplicative_2955_ = lean_ctor_get(v_inst_2952_, 0);
v_toBind_2956_ = lean_ctor_get(v_inst_2952_, 1);
lean_inc_n(v_toBind_2956_, 2);
v_toPure_2957_ = lean_ctor_get(v_toApplicative_2955_, 1);
lean_inc(v_toPure_2957_);
lean_inc_ref(v_inst_2953_);
v___x_2958_ = l_Lean_getRefPos___redArg(v_inst_2952_, v_inst_2953_);
v___f_2959_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2959_, 0, v_ex_2954_);
lean_closure_set(v___f_2959_, 1, v_toPure_2957_);
lean_closure_set(v___f_2959_, 2, v_inst_2953_);
lean_closure_set(v___f_2959_, 3, v_toBind_2956_);
v___x_2960_ = lean_apply_4(v_toBind_2956_, lean_box(0), lean_box(0), v___x_2958_, v___f_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_ex_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2962_, v_inst_2963_, v_ex_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2966_, v_inst_2967_, v_x_2968_);
return v___x_2969_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2972_ = l_Lean_stringToMessageData(v___x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_____do__lift_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2977_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_msg_2973_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Lean_toMessageList(v_____do__lift_2976_);
v___x_2980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2978_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = l_Lean_throwError___redArg(v_inst_2974_, v_inst_2975_, v___x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_msg_2985_, lean_object* v_exs_2986_){
_start:
{
lean_object* v_toBind_2987_; lean_object* v___f_2988_; lean_object* v___f_2989_; size_t v_sz_2990_; size_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_toBind_2987_ = lean_ctor_get(v_inst_2983_, 1);
lean_inc(v_toBind_2987_);
lean_inc_ref_n(v_inst_2983_, 2);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2988_, 0, v_inst_2983_);
lean_closure_set(v___f_2988_, 1, v_inst_2984_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2989_, 0, v_msg_2985_);
lean_closure_set(v___f_2989_, 1, v_inst_2983_);
lean_closure_set(v___f_2989_, 2, v_inst_2982_);
v_sz_2990_ = lean_array_size(v_exs_2986_);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2983_, v___f_2988_, v_sz_2990_, v___x_2991_, v_exs_2986_);
v___x_2993_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2992_, v___f_2989_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2994_, lean_object* v_00_u03b1_2995_, lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_msg_2999_, lean_object* v_exs_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2996_, v_inst_2997_, v_inst_2998_, v_msg_2999_, v_exs_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3069_ = 0;
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3071_ = l_Lean_registerTraceClass(v___x_3068_, v___x_3069_, v___x_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v___x_3071_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3073_ = l_Lean_registerTraceClass(v___x_3072_, v___x_3069_, v___x_3070_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref(v___x_3073_);
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3075_ = 1;
v___x_3076_ = l_Lean_registerTraceClass(v___x_3074_, v___x_3075_, v___x_3070_);
return v___x_3076_;
}
else
{
return v___x_3073_;
}
}
else
{
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3078_;
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
