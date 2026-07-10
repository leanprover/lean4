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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "macroAttribute"};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_expandOptNamedPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 124, 3, 111, 194, 84, 182, 133)}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_macroAttribute;
static const lean_string_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 391, .m_capacity = 391, .m_length = 388, .m_data = "Registers a macro expander for a given syntax node kind.\n\nA macro expander should have type `Lean.Macro` (which is `Lean.Syntax → Lean.MacroM Lean.Syntax`),\ni.e. should take syntax of the given syntax node kind as a parameter and produce different syntax\nin the same syntax category.\n\nThe `macro_rules` and `macro` commands should usually be preferred over using this attribute\ndirectly.\n"};
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
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(lean_object* v___x_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v_head_104_; lean_object* v_tail_105_; lean_object* v_before_106_; uint8_t v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; 
v_head_104_ = lean_ctor_get(v_x_102_, 0);
v_tail_105_ = lean_ctor_get(v_x_102_, 1);
v_before_106_ = lean_ctor_get(v_head_104_, 0);
v___x_107_ = 0;
v___x_108_ = l_Lean_Syntax_getPos_x3f(v_before_106_, v___x_107_);
v___x_109_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v___x_108_, v___x_101_);
lean_dec(v___x_108_);
v___x_110_ = lean_bool_not(v___x_109_);
if (v___x_110_ == 0)
{
v_x_102_ = v_tail_105_;
goto _start;
}
else
{
lean_object* v___x_112_; 
lean_inc(v_head_104_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_head_104_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(lean_object* v___x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v___x_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* v_ref_116_, lean_object* v_macroStack_117_){
_start:
{
uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = 0;
v___x_119_ = l_Lean_Syntax_getPos_x3f(v_ref_116_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
v___x_120_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_119_, v_macroStack_117_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_inc(v_ref_116_);
return v_ref_116_;
}
else
{
lean_object* v_val_121_; lean_object* v_before_122_; 
v_val_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_120_, 1);
v_before_122_ = lean_ctor_get(v_val_121_, 0);
lean_inc(v_before_122_);
lean_dec(v_val_121_);
return v_before_122_;
}
}
else
{
lean_dec_ref_known(v___x_119_, 1);
lean_inc(v_ref_116_);
return v_ref_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* v_ref_123_, lean_object* v_macroStack_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Elab_getBetterRef(v_ref_123_, v_macroStack_124_);
lean_dec(v_macroStack_124_);
lean_dec(v_ref_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object* v_name_126_, lean_object* v_decl_127_, lean_object* v_ref_128_){
_start:
{
lean_object* v_defValue_130_; lean_object* v_descr_131_; lean_object* v_deprecation_x3f_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_defValue_130_ = lean_ctor_get(v_decl_127_, 0);
v_descr_131_ = lean_ctor_get(v_decl_127_, 1);
v_deprecation_x3f_132_ = lean_ctor_get(v_decl_127_, 2);
v___x_133_ = lean_alloc_ctor(1, 0, 1);
v___x_134_ = lean_unbox(v_defValue_130_);
lean_ctor_set_uint8(v___x_133_, 0, v___x_134_);
lean_inc(v_deprecation_x3f_132_);
lean_inc_ref(v_descr_131_);
lean_inc_n(v_name_126_, 2);
v___x_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_135_, 0, v_name_126_);
lean_ctor_set(v___x_135_, 1, v_ref_128_);
lean_ctor_set(v___x_135_, 2, v___x_133_);
lean_ctor_set(v___x_135_, 3, v_descr_131_);
lean_ctor_set(v___x_135_, 4, v_deprecation_x3f_132_);
v___x_136_ = lean_register_option(v_name_126_, v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_136_, 0);
lean_dec(v_unused_145_);
v___x_138_ = v___x_136_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_dec(v___x_136_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_defValue_130_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_name_126_);
lean_ctor_set(v___x_140_, 1, v_defValue_130_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_name_126_);
v_a_146_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_136_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_136_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_154_, lean_object* v_decl_155_, lean_object* v_ref_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_154_, v_decl_155_, v_ref_156_);
lean_dec_ref(v_decl_155_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_179_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_180_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_177_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
return v_res_182_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1));
v___x_187_ = l_Lean_MessageData_ofFormat(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0(lean_object* v___x_188_, lean_object* v_msgData_189_, lean_object* v_elem_190_){
_start:
{
lean_object* v_before_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
v_before_191_ = lean_ctor_get(v_elem_190_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_elem_190_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_elem_190_, 1);
lean_dec(v_unused_204_);
v___x_193_ = v_elem_190_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_before_191_);
lean_dec(v_elem_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 7);
lean_ctor_set(v___x_193_, 1, v___x_188_);
lean_ctor_set(v___x_193_, 0, v_msgData_189_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_msgData_189_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_188_);
v___x_196_ = v_reuseFailAlloc_202_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2, &l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_MessageData_ofSyntax(v_before_191_);
v___x_200_ = l_Lean_indentD(v___x_199_);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_198_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_box(1);
v___x_206_ = l_Lean_MessageData_ofFormat(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___f_208_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__0), 3, 1);
lean_closure_set(v___f_208_, 0, v___x_207_);
return v___f_208_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3));
v___x_213_ = l_Lean_MessageData_ofFormat(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_214_, lean_object* v_macroStack_215_, lean_object* v_toApplicative_216_, lean_object* v_msgData_217_, lean_object* v_____do__lift_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; 
v___x_219_ = l_Lean_Elab_pp_macroStack;
v___x_220_ = l_Lean_Option_get___redArg(v___x_214_, v_____do__lift_218_, v___x_219_);
v___x_221_ = lean_unbox(v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = lean_bool_not(v___x_221_);
if (v___x_222_ == 0)
{
if (lean_obj_tag(v_macroStack_215_) == 0)
{
lean_object* v_toPure_223_; lean_object* v___x_224_; 
v_toPure_223_ = lean_ctor_get(v_toApplicative_216_, 1);
lean_inc(v_toPure_223_);
lean_dec_ref(v_toApplicative_216_);
v___x_224_ = lean_apply_2(v_toPure_223_, lean_box(0), v_msgData_217_);
return v___x_224_;
}
else
{
lean_object* v_head_225_; lean_object* v_after_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_243_; 
v_head_225_ = lean_ctor_get(v_macroStack_215_, 0);
lean_inc(v_head_225_);
v_after_226_ = lean_ctor_get(v_head_225_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_head_225_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v_head_225_, 0);
lean_dec(v_unused_244_);
v___x_228_ = v_head_225_;
v_isShared_229_ = v_isSharedCheck_243_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_after_226_);
lean_dec(v_head_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_243_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_toPure_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_234_; 
v_toPure_230_ = lean_ctor_get(v_toApplicative_216_, 1);
lean_inc(v_toPure_230_);
lean_dec_ref(v_toApplicative_216_);
v___x_231_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_232_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 7);
lean_ctor_set(v___x_228_, 1, v___x_231_);
lean_ctor_set(v___x_228_, 0, v_msgData_217_);
v___x_234_ = v___x_228_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_msgData_217_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_231_);
v___x_234_ = v_reuseFailAlloc_242_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_msgData_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_235_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_MessageData_ofSyntax(v_after_226_);
v___x_238_ = l_Lean_indentD(v___x_237_);
v_msgData_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_239_, 0, v___x_236_);
lean_ctor_set(v_msgData_239_, 1, v___x_238_);
v___x_240_ = l_List_foldl___redArg(v___f_232_, v_msgData_239_, v_macroStack_215_);
v___x_241_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_240_);
return v___x_241_;
}
}
}
}
else
{
lean_object* v_toPure_245_; lean_object* v___x_246_; 
lean_dec(v_macroStack_215_);
v_toPure_245_ = lean_ctor_get(v_toApplicative_216_, 1);
lean_inc(v_toPure_245_);
lean_dec_ref(v_toApplicative_216_);
v___x_246_ = lean_apply_2(v_toPure_245_, lean_box(0), v_msgData_217_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_247_, lean_object* v_macroStack_248_, lean_object* v_toApplicative_249_, lean_object* v_msgData_250_, lean_object* v_____do__lift_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_247_, v_macroStack_248_, v_toApplicative_249_, v_msgData_250_, v_____do__lift_251_);
lean_dec_ref(v_____do__lift_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_msgData_255_, lean_object* v_macroStack_256_){
_start:
{
lean_object* v___x_257_; lean_object* v_toApplicative_258_; lean_object* v_toBind_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v___x_257_ = l_Lean_KVMap_instValueBool;
v_toApplicative_258_ = lean_ctor_get(v_inst_253_, 0);
lean_inc_ref(v_toApplicative_258_);
v_toBind_259_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_259_);
lean_dec_ref(v_inst_253_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_260_, 0, v___x_257_);
lean_closure_set(v___f_260_, 1, v_macroStack_256_);
lean_closure_set(v___f_260_, 2, v_toApplicative_258_);
lean_closure_set(v___f_260_, 3, v_msgData_255_);
v___x_261_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v_inst_254_, v___f_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_msgData_265_, lean_object* v_macroStack_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Elab_addMacroStack___redArg(v_inst_263_, v_inst_264_, v_msgData_265_, v_macroStack_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_____r_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_275_ = l_Lean_throwError___redArg(v_inst_271_, v_inst_272_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_276_, lean_object* v___f_277_, lean_object* v_toApplicative_278_, lean_object* v_____do__lift_279_){
_start:
{
uint8_t v___x_280_; 
lean_inc(v_k_276_);
v___x_280_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_279_, v_k_276_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_toApplicative_278_);
lean_dec(v_k_276_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_apply_1(v___f_277_, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v_toPure_283_; lean_object* v___x_284_; 
lean_dec(v___f_277_);
v_toPure_283_ = lean_ctor_get(v_toApplicative_278_, 1);
lean_inc(v_toPure_283_);
lean_dec_ref(v_toApplicative_278_);
v___x_284_ = lean_apply_2(v_toPure_283_, lean_box(0), v_k_276_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_285_, lean_object* v___f_286_, lean_object* v_toApplicative_287_, lean_object* v_toBind_288_, lean_object* v_getEnv_289_, lean_object* v_____do__lift_290_){
_start:
{
lean_object* v_k_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_k_291_ = l_Lean_mkPrivateName(v_____do__lift_290_, v_k_285_);
v___f_292_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_292_, 0, v_k_291_);
lean_closure_set(v___f_292_, 1, v___f_286_);
lean_closure_set(v___f_292_, 2, v_toApplicative_287_);
v___x_293_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v_getEnv_289_, v___f_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_294_, lean_object* v___f_295_, lean_object* v_toApplicative_296_, lean_object* v_toBind_297_, lean_object* v_getEnv_298_, lean_object* v_____do__lift_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_294_, v___f_295_, v_toApplicative_296_, v_toBind_297_, v_getEnv_298_, v_____do__lift_299_);
lean_dec_ref(v_____do__lift_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_301_, lean_object* v_toBind_302_, lean_object* v_getEnv_303_, lean_object* v___f_304_, lean_object* v_k_305_, lean_object* v_____do__lift_306_){
_start:
{
uint8_t v___y_308_; uint8_t v_isExporting_312_; uint8_t v___x_313_; 
v_isExporting_312_ = lean_ctor_get_uint8(v_____do__lift_306_, sizeof(void*)*8);
v___x_313_ = lean_bool_not(v_isExporting_312_);
if (v___x_313_ == 0)
{
v___y_308_ = v___x_313_;
goto v___jp_307_;
}
else
{
uint8_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = l_Lean_isPrivateName(v_k_305_);
v___x_315_ = lean_bool_not(v___x_314_);
v___y_308_ = v___x_315_;
goto v___jp_307_;
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v___f_304_);
lean_dec(v_getEnv_303_);
lean_dec(v_toBind_302_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_apply_1(v___f_301_, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
lean_dec(v___f_301_);
v___x_311_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v_getEnv_303_, v___f_304_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_316_, lean_object* v_toBind_317_, lean_object* v_getEnv_318_, lean_object* v___f_319_, lean_object* v_k_320_, lean_object* v_____do__lift_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_316_, v_toBind_317_, v_getEnv_318_, v___f_319_, v_k_320_, v_____do__lift_321_);
lean_dec_ref(v_____do__lift_321_);
lean_dec(v_k_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_323_, lean_object* v_toBind_324_, lean_object* v_getEnv_325_, lean_object* v___f_326_, lean_object* v_toApplicative_327_, lean_object* v_____do__lift_328_){
_start:
{
uint8_t v___x_329_; 
lean_inc(v_k_323_);
v___x_329_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_328_, v_k_323_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v_toApplicative_327_);
lean_dec(v_k_323_);
v___x_330_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v_getEnv_325_, v___f_326_);
return v___x_330_;
}
else
{
lean_object* v_toPure_331_; lean_object* v___x_332_; 
lean_dec(v___f_326_);
lean_dec(v_getEnv_325_);
lean_dec(v_toBind_324_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_331_);
lean_dec_ref(v_toApplicative_327_);
v___x_332_ = lean_apply_2(v_toPure_331_, lean_box(0), v_k_323_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_k_336_){
_start:
{
lean_object* v_toApplicative_337_; lean_object* v_toBind_338_; lean_object* v_getEnv_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; 
v_toApplicative_337_ = lean_ctor_get(v_inst_333_, 0);
lean_inc_ref_n(v_toApplicative_337_, 2);
v_toBind_338_ = lean_ctor_get(v_inst_333_, 1);
lean_inc_n(v_toBind_338_, 4);
v_getEnv_339_ = lean_ctor_get(v_inst_334_, 0);
lean_inc_n(v_getEnv_339_, 4);
lean_dec_ref(v_inst_334_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_340_, 0, v_inst_333_);
lean_closure_set(v___f_340_, 1, v_inst_335_);
lean_inc_ref(v___f_340_);
lean_inc_n(v_k_336_, 2);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_341_, 0, v_k_336_);
lean_closure_set(v___f_341_, 1, v___f_340_);
lean_closure_set(v___f_341_, 2, v_toApplicative_337_);
lean_closure_set(v___f_341_, 3, v_toBind_338_);
lean_closure_set(v___f_341_, 4, v_getEnv_339_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_342_, 0, v___f_340_);
lean_closure_set(v___f_342_, 1, v_toBind_338_);
lean_closure_set(v___f_342_, 2, v_getEnv_339_);
lean_closure_set(v___f_342_, 3, v___f_341_);
lean_closure_set(v___f_342_, 4, v_k_336_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 6, 5);
lean_closure_set(v___f_343_, 0, v_k_336_);
lean_closure_set(v___f_343_, 1, v_toBind_338_);
lean_closure_set(v___f_343_, 2, v_getEnv_339_);
lean_closure_set(v___f_343_, 3, v___f_342_);
lean_closure_set(v___f_343_, 4, v_toApplicative_337_);
v___x_344_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v_getEnv_339_, v___f_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_k_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_346_, v_inst_347_, v_inst_348_, v_k_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_k_354_, lean_object* v_pre_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_351_, v_inst_352_, v_inst_353_, v_k_354_, v_pre_355_, v_x_356_);
lean_dec_ref(v_x_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_k_361_, lean_object* v_x_362_){
_start:
{
switch(lean_obj_tag(v_x_362_))
{
case 1:
{
lean_object* v_toMonadExceptOf_363_; lean_object* v_pre_364_; lean_object* v_tryCatch_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_toMonadExceptOf_363_ = lean_ctor_get(v_inst_360_, 0);
v_pre_364_ = lean_ctor_get(v_x_362_, 0);
v_tryCatch_365_ = lean_ctor_get(v_toMonadExceptOf_363_, 1);
lean_inc(v_tryCatch_365_);
lean_inc(v_pre_364_);
lean_inc(v_k_361_);
lean_inc_ref(v_inst_360_);
lean_inc_ref(v_inst_359_);
lean_inc_ref(v_inst_358_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_366_, 0, v_inst_358_);
lean_closure_set(v___f_366_, 1, v_inst_359_);
lean_closure_set(v___f_366_, 2, v_inst_360_);
lean_closure_set(v___f_366_, 3, v_k_361_);
lean_closure_set(v___f_366_, 4, v_pre_364_);
v___x_367_ = l_Lean_Name_append(v_x_362_, v_k_361_);
v___x_368_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_358_, v_inst_359_, v_inst_360_, v___x_367_);
v___x_369_ = lean_apply_3(v_tryCatch_365_, lean_box(0), v___x_368_, v___f_366_);
return v___x_369_;
}
case 0:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_358_, v_inst_359_, v_inst_360_, v_k_361_);
return v___x_370_;
}
default: 
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_x_362_);
lean_dec(v_k_361_);
lean_dec_ref(v_inst_359_);
v___x_371_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_372_ = l_Lean_throwError___redArg(v_inst_358_, v_inst_360_, v___x_371_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_k_376_, lean_object* v_pre_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_373_, v_inst_374_, v_inst_375_, v_k_376_, v_pre_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_k_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_381_, v_inst_382_, v_inst_383_, v_k_384_, v_x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_387_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set(v___x_392_, 3, v___x_391_);
lean_ctor_set(v___x_392_, 4, v___x_390_);
lean_ctor_set(v___x_392_, 5, v___x_390_);
lean_ctor_set(v___x_392_, 6, v___x_390_);
lean_ctor_set(v___x_392_, 7, v___x_390_);
lean_ctor_set(v___x_392_, 8, v___x_390_);
lean_ctor_set(v___x_392_, 9, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(32u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_unsigned_to_nat(32u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_397_);
lean_ctor_set(v___x_401_, 3, v___x_397_);
lean_ctor_set_usize(v___x_401_, 4, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_box(1);
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_404_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_env_411_; lean_object* v_options_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_410_ = lean_st_ref_get(v___y_408_);
v_env_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_410_);
v_options_412_ = lean_ctor_get(v___y_407_, 2);
v___x_413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_412_);
v___x_415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_415_, 0, v_env_411_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_414_);
lean_ctor_set(v___x_415_, 3, v_options_412_);
v___x_416_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_msgData_406_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_ref_427_ = lean_ctor_get(v___y_424_, 5);
v___x_428_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_423_, v___y_424_, v___y_425_);
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_ref_427_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_ref_427_);
lean_ctor_set(v___x_433_, 1, v_a_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 1);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___x_452_; lean_object* v_env_453_; uint8_t v___x_454_; 
v___x_452_ = lean_st_ref_get(v___y_445_);
v_env_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_env_453_);
lean_dec(v___x_452_);
lean_inc(v_k_443_);
v___x_454_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_453_, v_k_443_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___y_457_; lean_object* v_env_465_; uint8_t v_isExporting_466_; uint8_t v___x_467_; 
v___x_455_ = lean_st_ref_get(v___y_445_);
v_env_465_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_455_);
v_isExporting_466_ = lean_ctor_get_uint8(v_env_465_, sizeof(void*)*8);
lean_dec_ref(v_env_465_);
v___x_467_ = lean_bool_not(v_isExporting_466_);
if (v___x_467_ == 0)
{
v___y_457_ = v___x_467_;
goto v___jp_456_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = l_Lean_isPrivateName(v_k_443_);
v___x_469_ = lean_bool_not(v___x_468_);
v___y_457_ = v___x_469_;
goto v___jp_456_;
}
v___jp_456_:
{
if (v___y_457_ == 0)
{
lean_dec(v_k_443_);
v___y_448_ = v___y_444_;
v___y_449_ = v___y_445_;
goto v___jp_447_;
}
else
{
lean_object* v___x_458_; lean_object* v_env_459_; lean_object* v___x_460_; lean_object* v_env_461_; lean_object* v_k_462_; uint8_t v___x_463_; 
v___x_458_ = lean_st_ref_get(v___y_445_);
v_env_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_459_);
lean_dec(v___x_458_);
v___x_460_ = lean_st_ref_get(v___y_445_);
v_env_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_env_461_);
lean_dec(v___x_460_);
v_k_462_ = l_Lean_mkPrivateName(v_env_459_, v_k_443_);
lean_dec_ref(v_env_459_);
lean_inc(v_k_462_);
v___x_463_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_461_, v_k_462_);
if (v___x_463_ == 0)
{
lean_dec(v_k_462_);
v___y_448_ = v___y_444_;
v___y_449_ = v___y_445_;
goto v___jp_447_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_k_462_);
return v___x_464_;
}
}
}
}
else
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_k_443_);
return v___x_470_;
}
v___jp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_451_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_450_, v___y_448_, v___y_449_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_476_, lean_object* v_x_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
switch(lean_obj_tag(v_x_477_))
{
case 1:
{
lean_object* v_pre_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_pre_481_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_pre_481_);
lean_inc(v_k_476_);
v___x_482_ = l_Lean_Name_append(v_x_477_, v_k_476_);
v___x_483_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_482_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec(v_pre_481_);
lean_dec(v_k_476_);
return v___x_483_;
}
else
{
lean_object* v_a_484_; uint8_t v___y_486_; uint8_t v___x_488_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
v___x_488_ = l_Lean_Exception_isInterrupt(v_a_484_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
v___x_489_ = l_Lean_Exception_isRuntime(v_a_484_);
v___y_486_ = v___x_489_;
goto v___jp_485_;
}
else
{
lean_dec(v_a_484_);
v___y_486_ = v___x_488_;
goto v___jp_485_;
}
v___jp_485_:
{
if (v___y_486_ == 0)
{
lean_dec_ref_known(v___x_483_, 1);
v_x_477_ = v_pre_481_;
goto _start;
}
else
{
lean_dec(v_pre_481_);
lean_dec(v_k_476_);
return v___x_483_;
}
}
}
}
case 0:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_476_, v___y_478_, v___y_479_);
return v___x_490_;
}
default: 
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_x_477_);
lean_dec(v_k_476_);
v___x_491_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_492_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_491_, v___y_478_, v___y_479_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_493_, lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_493_, v_x_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_currNamespace_503_; lean_object* v___x_504_; 
v_currNamespace_503_ = lean_ctor_get(v_a_500_, 6);
lean_inc(v_currNamespace_503_);
v___x_504_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_499_, v_currNamespace_503_, v_a_500_, v_a_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_516_, lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_516_, v_msg_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_528_, lean_object* v_stx_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Attribute_Builtin_getId(v_stx_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___y_536_; uint8_t v___y_537_; lean_object* v___x_544_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_n(v_a_534_, 2);
lean_dec_ref_known(v___x_533_, 1);
v___x_544_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_534_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec(v_a_534_);
lean_dec(v_defaultParserNamespace_528_);
return v___x_544_;
}
else
{
lean_object* v_a_545_; uint8_t v___y_547_; uint8_t v___x_553_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
v___x_553_ = l_Lean_Exception_isInterrupt(v_a_545_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Exception_isRuntime(v_a_545_);
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
else
{
lean_dec(v_a_545_);
v___y_547_ = v___x_553_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref_known(v___x_544_, 1);
lean_inc(v_a_534_);
v___x_548_ = l_Lean_Name_append(v_defaultParserNamespace_528_, v_a_534_);
v___x_549_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_548_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_dec(v_a_534_);
return v___x_549_;
}
else
{
lean_object* v_a_550_; uint8_t v___x_551_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
v___x_551_ = l_Lean_Exception_isInterrupt(v_a_550_);
if (v___x_551_ == 0)
{
uint8_t v___x_552_; 
v___x_552_ = l_Lean_Exception_isRuntime(v_a_550_);
v___y_536_ = v___x_549_;
v___y_537_ = v___x_552_;
goto v___jp_535_;
}
else
{
lean_dec(v_a_550_);
v___y_536_ = v___x_549_;
v___y_537_ = v___x_551_;
goto v___jp_535_;
}
}
}
else
{
lean_dec(v_a_534_);
lean_dec(v_defaultParserNamespace_528_);
return v___x_544_;
}
}
}
v___jp_535_:
{
if (v___y_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec_ref(v___y_536_);
v___x_538_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_539_ = l_Lean_MessageData_ofName(v_a_534_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_542_, v_a_530_, v_a_531_);
return v___x_543_;
}
else
{
lean_dec(v_a_534_);
return v___y_536_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_528_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_555_, lean_object* v_stx_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_555_, v_stx_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_565_, lean_object* v_opts_566_, lean_object* v_constName_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_569_ = l_Lean_Environment_evalConstCheck___redArg(v_env_565_, v_opts_566_, v___x_568_, v_constName_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_570_, lean_object* v_opts_571_, lean_object* v_constName_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_570_, v_opts_571_, v_constName_572_);
lean_dec_ref(v_opts_571_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_599_ = l_Lean_mkAtom(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_601_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_602_ = lean_array_push(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_612_ = l_Lean_mkAtom(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_614_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_615_ = lean_array_push(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_617_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_618_ = lean_box(2);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_621_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_622_ = lean_array_push(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_624_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_625_ = lean_box(2);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_628_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_629_ = lean_array_push(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_631_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_632_ = lean_box(2);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_630_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_635_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_636_ = lean_array_push(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_638_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_639_ = lean_box(2);
v___x_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
lean_ctor_set(v___x_640_, 2, v___x_637_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_642_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_643_ = lean_array_push(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_645_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_646_ = lean_box(2);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_644_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_649_, lean_object* v_declName_650_, lean_object* v_kind_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
if (v_builtin_649_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v_declName_650_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_650_, v___y_652_, v___y_653_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_658_, lean_object* v_declName_659_, lean_object* v_kind_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
uint8_t v_builtin_boxed_664_; lean_object* v_res_665_; 
v_builtin_boxed_664_ = lean_unbox(v_builtin_658_);
v_res_665_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_664_, v_declName_659_, v_kind_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v_kind_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; lean_object* v_infoState_670_; uint8_t v_enabled_671_; 
v___x_669_ = lean_st_ref_get(v___y_667_);
v_infoState_670_ = lean_ctor_get(v___x_669_, 7);
lean_inc_ref(v_infoState_670_);
lean_dec(v___x_669_);
v_enabled_671_ = lean_ctor_get_uint8(v_infoState_670_, sizeof(void*)*3);
lean_dec_ref(v_infoState_670_);
if (v_enabled_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec_ref(v_t_666_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v_infoState_675_; lean_object* v_env_676_; lean_object* v_nextMacroScope_677_; lean_object* v_ngen_678_; lean_object* v_auxDeclNGen_679_; lean_object* v_traceState_680_; lean_object* v_cache_681_; lean_object* v_messages_682_; lean_object* v_snapshotTasks_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_705_; 
v___x_674_ = lean_st_ref_take(v___y_667_);
v_infoState_675_ = lean_ctor_get(v___x_674_, 7);
v_env_676_ = lean_ctor_get(v___x_674_, 0);
v_nextMacroScope_677_ = lean_ctor_get(v___x_674_, 1);
v_ngen_678_ = lean_ctor_get(v___x_674_, 2);
v_auxDeclNGen_679_ = lean_ctor_get(v___x_674_, 3);
v_traceState_680_ = lean_ctor_get(v___x_674_, 4);
v_cache_681_ = lean_ctor_get(v___x_674_, 5);
v_messages_682_ = lean_ctor_get(v___x_674_, 6);
v_snapshotTasks_683_ = lean_ctor_get(v___x_674_, 8);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_705_ == 0)
{
v___x_685_ = v___x_674_;
v_isShared_686_ = v_isSharedCheck_705_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snapshotTasks_683_);
lean_inc(v_infoState_675_);
lean_inc(v_messages_682_);
lean_inc(v_cache_681_);
lean_inc(v_traceState_680_);
lean_inc(v_auxDeclNGen_679_);
lean_inc(v_ngen_678_);
lean_inc(v_nextMacroScope_677_);
lean_inc(v_env_676_);
lean_dec(v___x_674_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_705_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v_enabled_687_; lean_object* v_assignment_688_; lean_object* v_lazyAssignment_689_; lean_object* v_trees_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_704_; 
v_enabled_687_ = lean_ctor_get_uint8(v_infoState_675_, sizeof(void*)*3);
v_assignment_688_ = lean_ctor_get(v_infoState_675_, 0);
v_lazyAssignment_689_ = lean_ctor_get(v_infoState_675_, 1);
v_trees_690_ = lean_ctor_get(v_infoState_675_, 2);
v_isSharedCheck_704_ = !lean_is_exclusive(v_infoState_675_);
if (v_isSharedCheck_704_ == 0)
{
v___x_692_ = v_infoState_675_;
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_trees_690_);
lean_inc(v_lazyAssignment_689_);
lean_inc(v_assignment_688_);
lean_dec(v_infoState_675_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_PersistentArray_push___redArg(v_trees_690_, v_t_666_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 2, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_assignment_688_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_lazyAssignment_689_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v___x_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*3, v_enabled_687_);
v___x_696_ = v_reuseFailAlloc_703_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 7, v___x_696_);
v___x_698_ = v___x_685_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_env_676_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_nextMacroScope_677_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_ngen_678_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_auxDeclNGen_679_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_traceState_680_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_cache_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_messages_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v_snapshotTasks_683_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_st_ref_set(v___y_667_, v___x_698_);
v___x_700_ = lean_box(0);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_706_, v___y_707_);
lean_dec(v___y_707_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(32u);
v___x_711_ = lean_mk_empty_array_with_capacity(v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_713_ = ((size_t)5ULL);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_unsigned_to_nat(32u);
v___x_716_ = lean_mk_empty_array_with_capacity(v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_718_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_714_);
lean_ctor_set(v___x_718_, 3, v___x_714_);
lean_ctor_set_usize(v___x_718_, 4, v___x_713_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v_infoState_724_; uint8_t v_enabled_725_; 
v___x_723_ = lean_st_ref_get(v___y_721_);
v_infoState_724_ = lean_ctor_get(v___x_723_, 7);
lean_inc_ref(v_infoState_724_);
lean_dec(v___x_723_);
v_enabled_725_ = lean_ctor_get_uint8(v_infoState_724_, sizeof(void*)*3);
lean_dec_ref(v_infoState_724_);
if (v_enabled_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_t_719_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v_t_719_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_729_, v___y_721_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_735_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_741_ = l_Lean_stringToMessageData(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_757_, lean_object* v_declHint_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; uint8_t v___y_764_; uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_761_ = lean_st_ref_get(v___y_759_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v___x_820_ = l_Lean_Name_isAnonymous(v_declHint_758_);
v___x_821_ = lean_bool_not(v___x_820_);
if (v___x_821_ == 0)
{
v___y_764_ = v___x_821_;
goto v___jp_763_;
}
else
{
uint8_t v_isExporting_822_; 
v_isExporting_822_ = lean_ctor_get_uint8(v_env_762_, sizeof(void*)*8);
v___y_764_ = v_isExporting_822_;
goto v___jp_763_;
}
v___jp_763_:
{
if (v___y_764_ == 0)
{
lean_object* v___x_765_; 
lean_dec_ref(v_env_762_);
lean_dec(v_declHint_758_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v_msg_757_);
return v___x_765_;
}
else
{
uint8_t v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = 0;
lean_inc_ref(v_env_762_);
v___x_767_ = l_Lean_Environment_setExporting(v_env_762_, v___x_766_);
lean_inc(v_declHint_758_);
lean_inc_ref(v___x_767_);
v___x_768_ = l_Lean_Environment_contains(v___x_767_, v_declHint_758_, v___y_764_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_767_);
lean_dec_ref(v_env_762_);
lean_dec(v_declHint_758_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_msg_757_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_c_775_; lean_object* v___x_776_; 
v___x_770_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_771_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_772_ = l_Lean_Options_empty;
v___x_773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_773_, 0, v___x_767_);
lean_ctor_set(v___x_773_, 1, v___x_770_);
lean_ctor_set(v___x_773_, 2, v___x_771_);
lean_ctor_set(v___x_773_, 3, v___x_772_);
lean_inc(v_declHint_758_);
v___x_774_ = l_Lean_MessageData_ofConstName(v_declHint_758_, v___x_766_);
v_c_775_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_775_, 0, v___x_773_);
lean_ctor_set(v_c_775_, 1, v___x_774_);
v___x_776_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_762_, v_declHint_758_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_env_762_);
lean_dec(v_declHint_758_);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_c_775_);
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_MessageData_note(v___x_780_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v_msg_757_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_819_; 
v_val_784_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_819_ == 0)
{
v___x_786_ = v___x_776_;
v_isShared_787_ = v_isSharedCheck_819_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v___x_776_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_819_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_mod_791_; uint8_t v___x_792_; 
v___x_788_ = lean_box(0);
v___x_789_ = l_Lean_Environment_header(v_env_762_);
lean_dec_ref(v_env_762_);
v___x_790_ = l_Lean_EnvironmentHeader_moduleNames(v___x_789_);
v_mod_791_ = lean_array_get(v___x_788_, v___x_790_, v_val_784_);
lean_dec(v_val_784_);
lean_dec_ref(v___x_790_);
v___x_792_ = l_Lean_isPrivateName(v_declHint_758_);
lean_dec(v_declHint_758_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_c_775_);
v___x_795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_MessageData_ofName(v_mod_791_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_MessageData_note(v___x_800_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v_msg_757_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 0, v___x_802_);
v___x_804_ = v___x_786_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_806_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_c_775_);
v___x_808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_MessageData_ofName(v_mod_791_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_MessageData_note(v___x_813_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v_msg_757_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 0, v___x_815_);
v___x_817_ = v___x_786_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_823_, lean_object* v_declHint_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_823_, v_declHint_824_, v___y_825_);
lean_dec(v___y_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_828_, lean_object* v_declHint_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
v___x_833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_828_, v_declHint_829_, v___y_831_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_unknownIdentifierMessageTag;
v___x_839_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_844_, lean_object* v_declHint_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_844_, v_declHint_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_850_, lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_fileName_855_; lean_object* v_fileMap_856_; lean_object* v_options_857_; lean_object* v_currRecDepth_858_; lean_object* v_maxRecDepth_859_; lean_object* v_ref_860_; lean_object* v_currNamespace_861_; lean_object* v_openDecls_862_; lean_object* v_initHeartbeats_863_; lean_object* v_maxHeartbeats_864_; lean_object* v_quotContext_865_; lean_object* v_currMacroScope_866_; uint8_t v_diag_867_; lean_object* v_cancelTk_x3f_868_; uint8_t v_suppressElabErrors_869_; lean_object* v_inheritedTraceOptions_870_; lean_object* v_ref_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_fileName_855_ = lean_ctor_get(v___y_852_, 0);
v_fileMap_856_ = lean_ctor_get(v___y_852_, 1);
v_options_857_ = lean_ctor_get(v___y_852_, 2);
v_currRecDepth_858_ = lean_ctor_get(v___y_852_, 3);
v_maxRecDepth_859_ = lean_ctor_get(v___y_852_, 4);
v_ref_860_ = lean_ctor_get(v___y_852_, 5);
v_currNamespace_861_ = lean_ctor_get(v___y_852_, 6);
v_openDecls_862_ = lean_ctor_get(v___y_852_, 7);
v_initHeartbeats_863_ = lean_ctor_get(v___y_852_, 8);
v_maxHeartbeats_864_ = lean_ctor_get(v___y_852_, 9);
v_quotContext_865_ = lean_ctor_get(v___y_852_, 10);
v_currMacroScope_866_ = lean_ctor_get(v___y_852_, 11);
v_diag_867_ = lean_ctor_get_uint8(v___y_852_, sizeof(void*)*14);
v_cancelTk_x3f_868_ = lean_ctor_get(v___y_852_, 12);
v_suppressElabErrors_869_ = lean_ctor_get_uint8(v___y_852_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_870_ = lean_ctor_get(v___y_852_, 13);
v_ref_871_ = l_Lean_replaceRef(v_ref_850_, v_ref_860_);
lean_inc_ref(v_inheritedTraceOptions_870_);
lean_inc(v_cancelTk_x3f_868_);
lean_inc(v_currMacroScope_866_);
lean_inc(v_quotContext_865_);
lean_inc(v_maxHeartbeats_864_);
lean_inc(v_initHeartbeats_863_);
lean_inc(v_openDecls_862_);
lean_inc(v_currNamespace_861_);
lean_inc(v_maxRecDepth_859_);
lean_inc(v_currRecDepth_858_);
lean_inc_ref(v_options_857_);
lean_inc_ref(v_fileMap_856_);
lean_inc_ref(v_fileName_855_);
v___x_872_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_872_, 0, v_fileName_855_);
lean_ctor_set(v___x_872_, 1, v_fileMap_856_);
lean_ctor_set(v___x_872_, 2, v_options_857_);
lean_ctor_set(v___x_872_, 3, v_currRecDepth_858_);
lean_ctor_set(v___x_872_, 4, v_maxRecDepth_859_);
lean_ctor_set(v___x_872_, 5, v_ref_871_);
lean_ctor_set(v___x_872_, 6, v_currNamespace_861_);
lean_ctor_set(v___x_872_, 7, v_openDecls_862_);
lean_ctor_set(v___x_872_, 8, v_initHeartbeats_863_);
lean_ctor_set(v___x_872_, 9, v_maxHeartbeats_864_);
lean_ctor_set(v___x_872_, 10, v_quotContext_865_);
lean_ctor_set(v___x_872_, 11, v_currMacroScope_866_);
lean_ctor_set(v___x_872_, 12, v_cancelTk_x3f_868_);
lean_ctor_set(v___x_872_, 13, v_inheritedTraceOptions_870_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*14, v_diag_867_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*14 + 1, v_suppressElabErrors_869_);
v___x_873_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_851_, v___x_872_, v___y_853_);
lean_dec_ref_known(v___x_872_, 14);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_874_, lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_874_, v_msg_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_ref_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_880_, lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_a_887_; lean_object* v___x_888_; 
v___x_886_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_881_, v_declHint_882_, v___y_883_, v___y_884_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_886_);
v___x_888_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_880_, v_a_887_, v___y_883_, v___y_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_889_, lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_889_, v_msg_890_, v_declHint_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v_ref_889_);
return v_res_895_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_899_, lean_object* v_constName_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_904_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_905_ = 0;
lean_inc(v_constName_900_);
v___x_906_ = l_Lean_MessageData_ofConstName(v_constName_900_, v___x_905_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_899_, v___x_909_, v_constName_900_, v___y_901_, v___y_902_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_911_, lean_object* v_constName_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_911_, v_constName_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_ref_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_ref_921_; lean_object* v___x_922_; 
v_ref_921_ = lean_ctor_get(v___y_918_, 5);
v___x_922_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_921_, v_constName_917_, v___y_918_, v___y_919_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; lean_object* v_env_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_932_ = lean_st_ref_get(v___y_930_);
v_env_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc_ref(v_env_933_);
lean_dec(v___x_932_);
v___x_934_ = 0;
lean_inc(v_constName_928_);
v___x_935_ = l_Lean_Environment_findConstVal_x3f(v_env_933_, v_constName_928_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_928_, v___y_929_, v___y_930_);
return v___x_936_;
}
else
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_constName_928_);
v_val_937_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 0);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_val_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
if (lean_obj_tag(v_a_950_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = l_List_reverse___redArg(v_a_951_);
return v___x_952_;
}
else
{
lean_object* v_head_953_; lean_object* v_tail_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_963_; 
v_head_953_ = lean_ctor_get(v_a_950_, 0);
v_tail_954_ = lean_ctor_get(v_a_950_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_963_ == 0)
{
v___x_956_ = v_a_950_;
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_tail_954_);
lean_inc(v_head_953_);
lean_dec(v_a_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Lean_mkLevelParam(v_head_953_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_a_951_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_951_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v_a_950_ = v_tail_954_;
v_a_951_ = v___x_960_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
lean_inc(v_constName_964_);
v___x_968_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_980_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_980_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_980_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_980_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_levelParams_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v_levelParams_973_ = lean_ctor_get(v_a_969_, 1);
lean_inc(v_levelParams_973_);
lean_dec(v_a_969_);
v___x_974_ = lean_box(0);
v___x_975_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_973_, v___x_974_);
v___x_976_ = l_Lean_mkConst(v_constName_964_, v___x_975_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_976_);
v___x_978_ = v___x_971_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_constName_964_);
v_a_981_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_968_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_968_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_994_, lean_object* v_n_995_, lean_object* v_expectedType_x3f_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_995_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v_stx_994_);
v___x_1004_ = l_Lean_LocalContext_empty;
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1006_, 0, v___x_1003_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v_expectedType_x3f_996_);
lean_ctor_set(v___x_1006_, 3, v_a_1001_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*4, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*4 + 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
v___x_1008_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1007_, v___y_997_, v___y_998_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_expectedType_x3f_996_);
lean_dec(v_stx_994_);
v_a_1009_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1000_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1017_, lean_object* v_n_1018_, lean_object* v_expectedType_x3f_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1017_, v_n_1018_, v_expectedType_x3f_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1024_, lean_object* v_i_1025_, lean_object* v_k_1026_){
_start:
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_array_get_size(v_keys_1024_);
v___x_1028_ = lean_nat_dec_lt(v_i_1025_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_dec(v_i_1025_);
return v___x_1028_;
}
else
{
lean_object* v_k_x27_1029_; uint8_t v___x_1030_; 
v_k_x27_1029_ = lean_array_fget_borrowed(v_keys_1024_, v_i_1025_);
v___x_1030_ = l_Lean_instBEqExtraModUse_beq(v_k_1026_, v_k_x27_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_i_1025_, v___x_1031_);
lean_dec(v_i_1025_);
v_i_1025_ = v___x_1032_;
goto _start;
}
else
{
lean_dec(v_i_1025_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1034_, v_i_1035_, v_k_1036_);
lean_dec_ref(v_k_1036_);
lean_dec_ref(v_keys_1034_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1039_, size_t v_x_1040_, lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v_es_1042_; lean_object* v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; lean_object* v_j_1046_; lean_object* v___x_1047_; 
v_es_1042_ = lean_ctor_get(v_x_1039_, 0);
v___x_1043_ = lean_box(2);
v___x_1044_ = ((size_t)31ULL);
v___x_1045_ = lean_usize_land(v_x_1040_, v___x_1044_);
v_j_1046_ = lean_usize_to_nat(v___x_1045_);
v___x_1047_ = lean_array_get_borrowed(v___x_1043_, v_es_1042_, v_j_1046_);
lean_dec(v_j_1046_);
switch(lean_obj_tag(v___x_1047_))
{
case 0:
{
lean_object* v_key_1048_; uint8_t v___x_1049_; 
v_key_1048_ = lean_ctor_get(v___x_1047_, 0);
v___x_1049_ = l_Lean_instBEqExtraModUse_beq(v_x_1041_, v_key_1048_);
return v___x_1049_;
}
case 1:
{
lean_object* v_node_1050_; size_t v___x_1051_; size_t v___x_1052_; 
v_node_1050_ = lean_ctor_get(v___x_1047_, 0);
v___x_1051_ = ((size_t)5ULL);
v___x_1052_ = lean_usize_shift_right(v_x_1040_, v___x_1051_);
v_x_1039_ = v_node_1050_;
v_x_1040_ = v___x_1052_;
goto _start;
}
default: 
{
uint8_t v___x_1054_; 
v___x_1054_ = 0;
return v___x_1054_;
}
}
}
else
{
lean_object* v_ks_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_ks_1055_ = lean_ctor_get(v_x_1039_, 0);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1055_, v___x_1056_, v_x_1041_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
size_t v_x_6775__boxed_1061_; uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_x_6775__boxed_1061_ = lean_unbox_usize(v_x_1059_);
lean_dec(v_x_1059_);
v_res_1062_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1058_, v_x_6775__boxed_1061_, v_x_1060_);
lean_dec_ref(v_x_1060_);
lean_dec_ref(v_x_1058_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
uint64_t v___x_1066_; size_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = l_Lean_instHashableExtraModUse_hash(v_x_1065_);
v___x_1067_ = lean_uint64_to_usize(v___x_1066_);
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1064_, v___x_1067_, v_x_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1069_, v_x_1070_);
lean_dec_ref(v_x_1070_);
lean_dec_ref(v_x_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1073_; double v___x_1074_; 
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_float_of_nat(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1078_, lean_object* v_msg_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_ref_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1129_; 
v_ref_1083_ = lean_ctor_get(v___y_1080_, 5);
v___x_1084_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1079_, v___y_1080_, v___y_1081_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1129_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1129_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v_traceState_1090_; lean_object* v_env_1091_; lean_object* v_nextMacroScope_1092_; lean_object* v_ngen_1093_; lean_object* v_auxDeclNGen_1094_; lean_object* v_cache_1095_; lean_object* v_messages_1096_; lean_object* v_infoState_1097_; lean_object* v_snapshotTasks_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1128_; 
v___x_1089_ = lean_st_ref_take(v___y_1081_);
v_traceState_1090_ = lean_ctor_get(v___x_1089_, 4);
v_env_1091_ = lean_ctor_get(v___x_1089_, 0);
v_nextMacroScope_1092_ = lean_ctor_get(v___x_1089_, 1);
v_ngen_1093_ = lean_ctor_get(v___x_1089_, 2);
v_auxDeclNGen_1094_ = lean_ctor_get(v___x_1089_, 3);
v_cache_1095_ = lean_ctor_get(v___x_1089_, 5);
v_messages_1096_ = lean_ctor_get(v___x_1089_, 6);
v_infoState_1097_ = lean_ctor_get(v___x_1089_, 7);
v_snapshotTasks_1098_ = lean_ctor_get(v___x_1089_, 8);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_snapshotTasks_1098_);
lean_inc(v_infoState_1097_);
lean_inc(v_messages_1096_);
lean_inc(v_cache_1095_);
lean_inc(v_traceState_1090_);
lean_inc(v_auxDeclNGen_1094_);
lean_inc(v_ngen_1093_);
lean_inc(v_nextMacroScope_1092_);
lean_inc(v_env_1091_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
uint64_t v_tid_1102_; lean_object* v_traces_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1127_; 
v_tid_1102_ = lean_ctor_get_uint64(v_traceState_1090_, sizeof(void*)*1);
v_traces_1103_ = lean_ctor_get(v_traceState_1090_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_traceState_1090_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1105_ = v_traceState_1090_;
v_isShared_1106_ = v_isSharedCheck_1127_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_traces_1103_);
lean_dec(v_traceState_1090_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1127_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; double v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1109_ = 0;
v___x_1110_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1111_, 0, v_cls_1078_);
lean_ctor_set(v___x_1111_, 1, v___x_1107_);
lean_ctor_set(v___x_1111_, 2, v___x_1110_);
lean_ctor_set_float(v___x_1111_, sizeof(void*)*3, v___x_1108_);
lean_ctor_set_float(v___x_1111_, sizeof(void*)*3 + 8, v___x_1108_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*3 + 16, v___x_1109_);
v___x_1112_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1113_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v_a_1085_);
lean_ctor_set(v___x_1113_, 2, v___x_1112_);
lean_inc(v_ref_1083_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_ref_1083_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_PersistentArray_push___redArg(v_traces_1103_, v___x_1114_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1115_);
v___x_1117_ = v___x_1105_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1115_);
lean_ctor_set_uint64(v_reuseFailAlloc_1126_, sizeof(void*)*1, v_tid_1102_);
v___x_1117_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 4, v___x_1117_);
v___x_1119_ = v___x_1100_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_env_1091_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_nextMacroScope_1092_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_ngen_1093_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_auxDeclNGen_1094_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v_cache_1095_);
lean_ctor_set(v_reuseFailAlloc_1125_, 6, v_messages_1096_);
lean_ctor_set(v_reuseFailAlloc_1125_, 7, v_infoState_1097_);
lean_ctor_set(v_reuseFailAlloc_1125_, 8, v_snapshotTasks_1098_);
v___x_1119_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_st_ref_set(v___y_1081_, v___x_1119_);
v___x_1121_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1121_);
v___x_1123_ = v___x_1087_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1130_, lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1130_, v_msg_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1135_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1139_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1140_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_cls_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1162_ = l_Lean_Name_append(v___x_1161_, v_cls_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1173_, uint8_t v_isMeta_1174_, lean_object* v_hint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_env_1180_; uint8_t v_isExporting_1181_; lean_object* v___x_1182_; lean_object* v_env_1183_; lean_object* v___x_1184_; lean_object* v_entry_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___y_1190_; lean_object* v___x_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1179_ = lean_st_ref_get(v___y_1177_);
v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_env_1180_);
lean_dec(v___x_1179_);
v_isExporting_1181_ = lean_ctor_get_uint8(v_env_1180_, sizeof(void*)*8);
lean_dec_ref(v_env_1180_);
v___x_1182_ = lean_st_ref_get(v___y_1177_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1173_);
v_entry_1185_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1185_, 0, v_mod_1173_);
lean_ctor_set_uint8(v_entry_1185_, sizeof(void*)*1, v_isExporting_1181_);
lean_ctor_set_uint8(v_entry_1185_, sizeof(void*)*1 + 1, v_isMeta_1174_);
v___x_1186_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1187_ = lean_box(1);
v___x_1188_ = lean_box(0);
v___x_1215_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1184_, v___x_1186_, v_env_1183_, v___x_1187_, v___x_1188_);
v___x_1216_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1215_, v_entry_1185_);
lean_dec(v___x_1215_);
v___x_1217_ = lean_bool_not(v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref_known(v_entry_1185_, 1);
lean_dec(v_hint_1175_);
lean_dec(v_mod_1173_);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
else
{
lean_object* v_options_1220_; uint8_t v_hasTrace_1221_; 
v_options_1220_ = lean_ctor_get(v___y_1176_, 2);
v_hasTrace_1221_ = lean_ctor_get_uint8(v_options_1220_, sizeof(void*)*1);
if (v_hasTrace_1221_ == 0)
{
lean_dec(v_hint_1175_);
lean_dec(v_mod_1173_);
v___y_1190_ = v___y_1177_;
goto v___jp_1189_;
}
else
{
lean_object* v_inheritedTraceOptions_1222_; lean_object* v_cls_1223_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_inheritedTraceOptions_1222_ = lean_ctor_get(v___y_1176_, 13);
v_cls_1223_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1243_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
v___x_1244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1222_, v_options_1220_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v_hint_1175_);
lean_dec(v_mod_1173_);
v___y_1190_ = v___y_1177_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1245_; lean_object* v___y_1247_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
if (v_isExporting_1181_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22));
v___y_1247_ = v___x_1254_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1255_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23));
v___y_1247_ = v___x_1255_;
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_inc_ref(v___y_1247_);
v___x_1248_ = l_Lean_stringToMessageData(v___y_1247_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1245_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
if (v_isMeta_1174_ == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1230_ = v___x_1251_;
v___y_1231_ = v___x_1252_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21));
v___y_1230_ = v___x_1251_;
v___y_1231_ = v___x_1253_;
goto v___jp_1229_;
}
}
}
v___jp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___y_1225_);
lean_ctor_set(v___x_1227_, 1, v___y_1226_);
v___x_1228_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1223_, v___x_1227_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref_known(v___x_1228_, 1);
v___y_1190_ = v___y_1177_;
goto v___jp_1189_;
}
else
{
lean_dec_ref_known(v_entry_1185_, 1);
return v___x_1228_;
}
}
v___jp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
lean_inc_ref(v___y_1231_);
v___x_1232_ = l_Lean_stringToMessageData(v___y_1231_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1230_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_MessageData_ofName(v_mod_1173_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_Name_isAnonymous(v_hint_1175_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1240_ = l_Lean_MessageData_ofName(v_hint_1175_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___y_1225_ = v___x_1237_;
v___y_1226_ = v___x_1241_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_hint_1175_);
v___x_1242_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1225_ = v___x_1237_;
v___y_1226_ = v___x_1242_;
goto v___jp_1224_;
}
}
}
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v_toEnvExtension_1192_; lean_object* v_env_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v_ngen_1195_; lean_object* v_auxDeclNGen_1196_; lean_object* v_traceState_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1213_; 
v___x_1191_ = lean_st_ref_take(v___y_1190_);
v_toEnvExtension_1192_ = lean_ctor_get(v___x_1186_, 0);
v_env_1193_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1195_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1196_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1197_ = lean_ctor_get(v___x_1191_, 4);
v_messages_1198_ = lean_ctor_get(v___x_1191_, 6);
v_infoState_1199_ = lean_ctor_get(v___x_1191_, 7);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1191_, 8);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1214_);
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_traceState_1197_);
lean_inc(v_auxDeclNGen_1196_);
lean_inc(v_ngen_1195_);
lean_inc(v_nextMacroScope_1194_);
lean_inc(v_env_1193_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1213_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_asyncMode_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v_asyncMode_1204_ = lean_ctor_get(v_toEnvExtension_1192_, 2);
v___x_1205_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1186_, v_env_1193_, v_entry_1185_, v_asyncMode_1204_, v___x_1188_);
v___x_1206_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1206_);
lean_ctor_set(v___x_1202_, 0, v___x_1205_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_nextMacroScope_1194_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_ngen_1195_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_auxDeclNGen_1196_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_traceState_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 6, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1212_, 7, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 8, v_snapshotTasks_1200_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_st_ref_set(v___y_1190_, v___x_1208_);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1256_, lean_object* v_isMeta_1257_, lean_object* v_hint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_isMeta_boxed_1262_; lean_object* v_res_1263_; 
v_isMeta_boxed_1262_ = lean_unbox(v_isMeta_1257_);
v_res_1263_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1256_, v_isMeta_boxed_1262_, v_hint_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1264_, lean_object* v_declName_1265_, lean_object* v_as_1266_, size_t v_sz_1267_, size_t v_i_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_lt(v_i_1268_, v_sz_1267_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec(v_declName_1265_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_b_1269_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v_modules_1276_; lean_object* v___x_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v_toImport_1280_; lean_object* v_module_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1275_ = l_Lean_Environment_header(v___x_1264_);
v_modules_1276_ = lean_ctor_get(v___x_1275_, 3);
lean_inc_ref(v_modules_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1278_ = lean_array_uget_borrowed(v_as_1266_, v_i_1268_);
v___x_1279_ = lean_array_get(v___x_1277_, v_modules_1276_, v_a_1278_);
lean_dec_ref(v_modules_1276_);
v_toImport_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref(v_toImport_1280_);
lean_dec(v___x_1279_);
v_module_1281_ = lean_ctor_get(v_toImport_1280_, 0);
lean_inc(v_module_1281_);
lean_dec_ref(v_toImport_1280_);
v___x_1282_ = 0;
lean_inc(v_declName_1265_);
v___x_1283_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1281_, v___x_1282_, v_declName_1265_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; 
lean_dec_ref_known(v___x_1283_, 1);
v___x_1284_ = lean_box(0);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1268_, v___x_1285_);
v_i_1268_ = v___x_1286_;
v_b_1269_ = v___x_1284_;
goto _start;
}
else
{
lean_dec(v_declName_1265_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1288_, lean_object* v_declName_1289_, lean_object* v_as_1290_, lean_object* v_sz_1291_, lean_object* v_i_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
size_t v_sz_boxed_1297_; size_t v_i_boxed_1298_; lean_object* v_res_1299_; 
v_sz_boxed_1297_ = lean_unbox_usize(v_sz_1291_);
lean_dec(v_sz_1291_);
v_i_boxed_1298_ = lean_unbox_usize(v_i_1292_);
lean_dec(v_i_1292_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1288_, v_declName_1289_, v_as_1290_, v_sz_boxed_1297_, v_i_boxed_1298_, v_b_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_as_1290_);
lean_dec_ref(v___x_1288_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
else
{
lean_object* v_key_1303_; lean_object* v_value_1304_; lean_object* v_tail_1305_; uint8_t v___x_1306_; 
v_key_1303_ = lean_ctor_get(v_x_1301_, 0);
v_value_1304_ = lean_ctor_get(v_x_1301_, 1);
v_tail_1305_ = lean_ctor_get(v_x_1301_, 2);
v___x_1306_ = lean_name_eq(v_key_1303_, v_a_1300_);
if (v___x_1306_ == 0)
{
v_x_1301_ = v_tail_1305_;
goto _start;
}
else
{
lean_object* v___x_1308_; 
lean_inc(v_value_1304_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_value_1304_);
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1309_, v_x_1310_);
lean_dec(v_x_1310_);
lean_dec(v_a_1309_);
return v_res_1311_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1312_; uint64_t v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(1723u);
v___x_1313_ = lean_uint64_of_nat(v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_buckets_1316_; lean_object* v___x_1317_; uint64_t v___y_1319_; 
v_buckets_1316_ = lean_ctor_get(v_m_1314_, 1);
v___x_1317_ = lean_array_get_size(v_buckets_1316_);
if (lean_obj_tag(v_a_1315_) == 0)
{
uint64_t v___x_1333_; 
v___x_1333_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1319_ = v___x_1333_;
goto v___jp_1318_;
}
else
{
uint64_t v_hash_1334_; 
v_hash_1334_ = lean_ctor_get_uint64(v_a_1315_, sizeof(void*)*2);
v___y_1319_ = v_hash_1334_;
goto v___jp_1318_;
}
v___jp_1318_:
{
uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v_fold_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1320_ = 32ULL;
v___x_1321_ = lean_uint64_shift_right(v___y_1319_, v___x_1320_);
v_fold_1322_ = lean_uint64_xor(v___y_1319_, v___x_1321_);
v___x_1323_ = 16ULL;
v___x_1324_ = lean_uint64_shift_right(v_fold_1322_, v___x_1323_);
v___x_1325_ = lean_uint64_xor(v_fold_1322_, v___x_1324_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = lean_usize_of_nat(v___x_1317_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_usize_land(v___x_1326_, v___x_1329_);
v___x_1331_ = lean_array_uget_borrowed(v_buckets_1316_, v___x_1330_);
v___x_1332_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1315_, v___x_1331_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1335_, v_a_1336_);
lean_dec(v_a_1336_);
lean_dec_ref(v_m_1335_);
return v_res_1337_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1341_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1342_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1345_, uint8_t v_isMeta_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_env_1354_; lean_object* v___y_1356_; lean_object* v___x_1369_; 
v___x_1350_ = lean_st_ref_get(v___y_1348_);
v_env_1354_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_env_1354_);
lean_dec(v___x_1350_);
v___x_1369_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1354_, v_declName_1345_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec_ref(v_env_1354_);
lean_dec(v_declName_1345_);
goto v___jp_1351_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1371_; lean_object* v_modules_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = l_Lean_Environment_header(v_env_1354_);
v_modules_1372_ = lean_ctor_get(v___x_1371_, 3);
lean_inc_ref(v_modules_1372_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = lean_array_get_size(v_modules_1372_);
v___x_1374_ = lean_nat_dec_lt(v_val_1370_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v_modules_1372_);
lean_dec(v_val_1370_);
lean_dec_ref(v_env_1354_);
lean_dec(v_declName_1345_);
goto v___jp_1351_;
}
else
{
lean_object* v___x_1375_; lean_object* v_env_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___y_1380_; 
v___x_1375_ = lean_st_ref_get(v___y_1348_);
v_env_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1376_);
lean_dec(v___x_1375_);
v___x_1377_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1378_ = lean_array_fget(v_modules_1372_, v_val_1370_);
lean_dec(v_val_1370_);
lean_dec_ref(v_modules_1372_);
if (v_isMeta_1346_ == 0)
{
lean_dec_ref(v_env_1376_);
v___y_1380_ = v_isMeta_1346_;
goto v___jp_1379_;
}
else
{
uint8_t v___x_1391_; uint8_t v___x_1392_; 
lean_inc(v_declName_1345_);
v___x_1391_ = l_Lean_isMarkedMeta(v_env_1376_, v_declName_1345_);
v___x_1392_ = lean_bool_not(v___x_1391_);
v___y_1380_ = v___x_1392_;
goto v___jp_1379_;
}
v___jp_1379_:
{
lean_object* v_toImport_1381_; lean_object* v_module_1382_; lean_object* v___x_1383_; 
v_toImport_1381_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_ref(v_toImport_1381_);
lean_dec(v___x_1378_);
v_module_1382_ = lean_ctor_get(v_toImport_1381_, 0);
lean_inc(v_module_1382_);
lean_dec_ref(v_toImport_1381_);
lean_inc(v_declName_1345_);
v___x_1383_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1382_, v___y_1380_, v_declName_1345_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec_ref_known(v___x_1383_, 1);
v___x_1384_ = l_Lean_indirectModUseExt;
v___x_1385_ = lean_box(1);
v___x_1386_ = lean_box(0);
lean_inc_ref(v_env_1354_);
v___x_1387_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1377_, v___x_1384_, v_env_1354_, v___x_1385_, v___x_1386_);
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1387_, v_declName_1345_);
lean_dec(v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1356_ = v___x_1389_;
goto v___jp_1355_;
}
else
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1388_, 1);
v___y_1356_ = v_val_1390_;
goto v___jp_1355_;
}
}
else
{
lean_dec_ref(v_env_1354_);
lean_dec(v_declName_1345_);
return v___x_1383_;
}
}
}
}
v___jp_1351_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_box(0);
v_sz_1358_ = lean_array_size(v___y_1356_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1354_, v_declName_1345_, v___y_1356_, v_sz_1358_, v___x_1359_, v___x_1357_, v___y_1347_, v___y_1348_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v_env_1354_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1368_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1357_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1357_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1393_, lean_object* v_isMeta_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_isMeta_boxed_1398_; lean_object* v_res_1399_; 
v_isMeta_boxed_1398_ = lean_unbox(v_isMeta_1394_);
v_res_1399_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1393_, v_isMeta_boxed_1398_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1400_, uint8_t v_x_1401_, lean_object* v_stx_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
lean_inc(v_stx_1402_);
v___x_1406_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1400_, v_stx_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1459_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1459_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1459_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v_env_1412_; uint8_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1411_ = lean_st_ref_get(v___y_1404_);
v_env_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_ref(v_env_1412_);
lean_dec(v___x_1411_);
v___x_1413_ = 1;
lean_inc(v_a_1407_);
v___x_1414_ = l_Lean_Environment_contains(v_env_1412_, v_a_1407_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1416_; 
lean_dec(v_stx_1402_);
if (v_isShared_1410_ == 0)
{
v___x_1416_ = v___x_1409_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1407_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
uint8_t v___x_1418_; lean_object* v___x_1419_; 
lean_del_object(v___x_1409_);
v___x_1418_ = 0;
lean_inc(v_a_1407_);
v___x_1419_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1407_, v___x_1418_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1450_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1449_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1449_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v_infoState_1424_; uint8_t v_enabled_1425_; 
v___x_1423_ = lean_st_ref_get(v___y_1404_);
v_infoState_1424_ = lean_ctor_get(v___x_1423_, 7);
lean_inc_ref(v_infoState_1424_);
lean_dec(v___x_1423_);
v_enabled_1425_ = lean_ctor_get_uint8(v_infoState_1424_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1424_);
if (v_enabled_1425_ == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_stx_1402_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_a_1407_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1407_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1421_);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = l_Lean_Syntax_getArg(v_stx_1402_, v___x_1429_);
lean_dec(v_stx_1402_);
v___x_1431_ = lean_box(0);
lean_inc(v_a_1407_);
v___x_1432_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1430_, v_a_1407_, v___x_1431_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1440_);
v___x_1434_ = v___x_1432_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v___x_1432_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v_a_1407_);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1407_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1407_);
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1432_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1432_);
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
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_a_1407_);
lean_dec(v_stx_1402_);
v_a_1451_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1419_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1419_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1402_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1460_, lean_object* v_x_1461_, lean_object* v_stx_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_x_7369__boxed_1466_; lean_object* v_res_1467_; 
v_x_7369__boxed_1466_ = lean_unbox(v_x_1461_);
v_res_1467_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1460_, v_x_7369__boxed_1466_, v_stx_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1470_, lean_object* v_attrName_1471_, lean_object* v_parserNamespace_1472_, lean_object* v_typeName_1473_, lean_object* v_kind_1474_, lean_object* v_attrDeclName_1475_){
_start:
{
lean_object* v___f_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___f_1477_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1478_, 0, v_parserNamespace_1472_);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1480_ = lean_string_append(v_kind_1474_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1481_, 0, v_attrBuiltinName_1470_);
lean_ctor_set(v___x_1481_, 1, v_attrName_1471_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
lean_ctor_set(v___x_1481_, 3, v_typeName_1473_);
lean_ctor_set(v___x_1481_, 4, v___f_1478_);
lean_ctor_set(v___x_1481_, 5, v___f_1477_);
v___x_1482_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1481_, v_attrDeclName_1475_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1483_, lean_object* v_attrName_1484_, lean_object* v_parserNamespace_1485_, lean_object* v_typeName_1486_, lean_object* v_kind_1487_, lean_object* v_attrDeclName_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1483_, v_attrName_1484_, v_parserNamespace_1485_, v_typeName_1486_, v_kind_1487_, v_attrDeclName_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1491_, lean_object* v_attrBuiltinName_1492_, lean_object* v_attrName_1493_, lean_object* v_parserNamespace_1494_, lean_object* v_typeName_1495_, lean_object* v_kind_1496_, lean_object* v_attrDeclName_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1492_, v_attrName_1493_, v_parserNamespace_1494_, v_typeName_1495_, v_kind_1496_, v_attrDeclName_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1500_, lean_object* v_attrBuiltinName_1501_, lean_object* v_attrName_1502_, lean_object* v_parserNamespace_1503_, lean_object* v_typeName_1504_, lean_object* v_kind_1505_, lean_object* v_attrDeclName_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1500_, v_attrBuiltinName_1501_, v_attrName_1502_, v_parserNamespace_1503_, v_typeName_1504_, v_kind_1505_, v_attrDeclName_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1509_, lean_object* v_m_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1510_, v_a_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1513_, lean_object* v_m_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1513_, v_m_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_m_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1517_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1528_, v_x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_res_1534_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1531_, v_x_1532_, v_x_1533_);
lean_dec_ref(v_x_1533_);
lean_dec_ref(v_x_1532_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1536_, lean_object* v_a_1537_, lean_object* v_x_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1537_, v_x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1540_, lean_object* v_a_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1540_, v_a_1541_, v_x_1542_);
lean_dec(v_x_1542_);
lean_dec(v_a_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1544_, lean_object* v_x_1545_, size_t v_x_1546_, lean_object* v_x_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1545_, v_x_1546_, v_x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
size_t v_x_7539__boxed_1553_; uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_x_7539__boxed_1553_ = lean_unbox_usize(v_x_1551_);
lean_dec(v_x_1551_);
v_res_1554_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1549_, v_x_1550_, v_x_7539__boxed_1553_, v_x_1552_);
lean_dec_ref(v_x_1552_);
lean_dec_ref(v_x_1550_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1556_, lean_object* v_constName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1557_, v___y_1558_, v___y_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_constName_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1562_, v_constName_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1568_, lean_object* v_keys_1569_, lean_object* v_vals_1570_, lean_object* v_heq_1571_, lean_object* v_i_1572_, lean_object* v_k_1573_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1569_, v_i_1572_, v_k_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1575_, lean_object* v_keys_1576_, lean_object* v_vals_1577_, lean_object* v_heq_1578_, lean_object* v_i_1579_, lean_object* v_k_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1575_, v_keys_1576_, v_vals_1577_, v_heq_1578_, v_i_1579_, v_k_1580_);
lean_dec_ref(v_k_1580_);
lean_dec_ref(v_vals_1577_);
lean_dec_ref(v_keys_1576_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1583_, lean_object* v_ref_1584_, lean_object* v_constName_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1584_, v_constName_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_ref_1591_, lean_object* v_constName_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1590_, v_ref_1591_, v_constName_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v_ref_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1597_, lean_object* v_ref_1598_, lean_object* v_msg_1599_, lean_object* v_declHint_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1598_, v_msg_1599_, v_declHint_1600_, v___y_1601_, v___y_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_ref_1606_, lean_object* v_msg_1607_, lean_object* v_declHint_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1605_, v_ref_1606_, v_msg_1607_, v_declHint_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v_ref_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1613_, lean_object* v_declHint_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1613_, v_declHint_1614_, v___y_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1619_, lean_object* v_declHint_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1619_, v_declHint_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1625_, lean_object* v_ref_1626_, lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1626_, v_msg_1627_, v___y_1628_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_ref_1633_, lean_object* v_msg_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1632_, v_ref_1633_, v_msg_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v_ref_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1651_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1652_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1653_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1654_ = lean_box(0);
v___x_1655_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1656_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1651_, v___x_1653_, v___x_1654_, v___x_1655_, v___x_1652_, v_ref_1649_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1667_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1673_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1674_ = l_Lean_addBuiltinDocString(v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1704_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1705_ = l_Lean_addBuiltinDeclarationRanges(v___x_1703_, v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1708_, lean_object* v_a_1709_, lean_object* v_____r_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_declName_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1724_; 
v_declName_1713_ = lean_ctor_get(v_toOLeanEntry_1708_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_toOLeanEntry_1708_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_toOLeanEntry_1708_, 0);
lean_dec(v_unused_1725_);
v___x_1715_ = v_toOLeanEntry_1708_;
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_declName_1713_);
lean_dec(v_toOLeanEntry_1708_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_a_1709_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1717_);
lean_ctor_set(v___x_1715_, 0, v_declName_1713_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_declName_1713_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___y_1712_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1726_, lean_object* v_a_1727_, lean_object* v_____r_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1726_, v_a_1727_, v_____r_1728_, v___y_1729_, v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1735_, lean_object* v_as_x27_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
if (lean_obj_tag(v_as_x27_1736_) == 0)
{
lean_object* v___x_1740_; 
lean_dec(v_stx_1735_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_b_1737_);
lean_ctor_set(v___x_1740_, 1, v___y_1739_);
return v___x_1740_;
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; lean_object* v_toOLeanEntry_1743_; uint8_t v_isBuiltin_1744_; lean_object* v_value_1745_; lean_object* v_macroScope_1746_; lean_object* v_traceMsgs_1747_; lean_object* v_expandedMacroDecls_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v_b_1737_);
v_head_1741_ = lean_ctor_get(v_as_x27_1736_, 0);
v_tail_1742_ = lean_ctor_get(v_as_x27_1736_, 1);
v_toOLeanEntry_1743_ = lean_ctor_get(v_head_1741_, 0);
v_isBuiltin_1744_ = lean_ctor_get_uint8(v_head_1741_, sizeof(void*)*2);
v_value_1745_ = lean_ctor_get(v_head_1741_, 1);
v_macroScope_1746_ = lean_ctor_get(v___y_1739_, 0);
v_traceMsgs_1747_ = lean_ctor_get(v___y_1739_, 1);
v_expandedMacroDecls_1748_ = lean_ctor_get(v___y_1739_, 2);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___y_1739_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1750_ = v___y_1739_;
v_isShared_1751_ = v_isSharedCheck_1812_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_expandedMacroDecls_1748_);
lean_inc(v_traceMsgs_1747_);
lean_inc(v_macroScope_1746_);
lean_dec(v___y_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1812_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_methods_1752_; lean_object* v_quotContext_1753_; lean_object* v_currRecDepth_1754_; lean_object* v_maxRecDepth_1755_; lean_object* v_ref_1756_; lean_object* v___x_1757_; lean_object* v_a_1759_; lean_object* v_a_1760_; lean_object* v___x_1764_; lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___y_1774_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v_methods_1752_ = lean_ctor_get(v___y_1738_, 0);
v_quotContext_1753_ = lean_ctor_get(v___y_1738_, 1);
v_currRecDepth_1754_ = lean_ctor_get(v___y_1738_, 3);
v_maxRecDepth_1755_ = lean_ctor_get(v___y_1738_, 4);
v_ref_1756_ = lean_ctor_get(v___y_1738_, 5);
v___x_1757_ = lean_box(0);
v___x_1764_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_nat_add(v_macroScope_1746_, v___x_1780_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1781_);
v___x_1783_ = v___x_1750_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_traceMsgs_1747_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_expandedMacroDecls_1748_);
v___x_1783_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1782_;
}
v___jp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1759_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v___x_1757_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1760_);
return v___x_1763_;
}
v___jp_1765_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
v_as_x27_1736_ = v_tail_1742_;
v_b_1737_ = v___x_1764_;
v___y_1739_ = v_a_1767_;
goto _start;
}
else
{
lean_object* v_declName_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v_stx_1735_);
v_declName_1769_ = lean_ctor_get(v_toOLeanEntry_1743_, 1);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_a_1766_);
lean_inc(v_declName_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_declName_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
v_a_1759_ = v___x_1772_;
v_a_1760_ = v_a_1767_;
goto v___jp_1758_;
}
}
v___jp_1773_:
{
lean_object* v_a_1775_; 
v_a_1775_ = lean_ctor_get(v___y_1774_, 0);
if (lean_obj_tag(v_a_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_a_1777_; 
lean_inc_ref(v_a_1775_);
lean_dec(v_stx_1735_);
v_a_1776_ = lean_ctor_get(v___y_1774_, 1);
lean_inc(v_a_1776_);
lean_dec_ref(v___y_1774_);
v_a_1777_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v_a_1775_, 1);
v_a_1759_ = v_a_1777_;
v_a_1760_ = v_a_1776_;
goto v___jp_1758_;
}
else
{
lean_object* v_a_1778_; 
v_a_1778_ = lean_ctor_get(v___y_1774_, 1);
lean_inc(v_a_1778_);
lean_dec_ref(v___y_1774_);
v_as_x27_1736_ = v_tail_1742_;
v_b_1737_ = v___x_1764_;
v___y_1739_ = v_a_1778_;
goto _start;
}
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_inc(v_ref_1756_);
lean_inc(v_maxRecDepth_1755_);
lean_inc(v_currRecDepth_1754_);
lean_inc(v_quotContext_1753_);
lean_inc(v_methods_1752_);
v___x_1784_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1784_, 0, v_methods_1752_);
lean_ctor_set(v___x_1784_, 1, v_quotContext_1753_);
lean_ctor_set(v___x_1784_, 2, v_macroScope_1746_);
lean_ctor_set(v___x_1784_, 3, v_currRecDepth_1754_);
lean_ctor_set(v___x_1784_, 4, v_maxRecDepth_1755_);
lean_ctor_set(v___x_1784_, 5, v_ref_1756_);
lean_inc(v_value_1745_);
lean_inc(v_stx_1735_);
v___x_1785_ = lean_apply_3(v_value_1745_, v_stx_1735_, v___x_1784_, v___x_1783_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1808_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_a_1787_ = lean_ctor_get(v___x_1785_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1789_ = v___x_1785_;
v_isShared_1790_ = v_isSharedCheck_1808_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1808_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_bool_not(v_isBuiltin_1744_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_del_object(v___x_1789_);
lean_inc_ref(v_toOLeanEntry_1743_);
v___x_1792_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1743_, v_a_1786_, v___x_1757_, v___y_1738_, v_a_1787_);
v___y_1774_ = v___x_1792_;
goto v___jp_1773_;
}
else
{
lean_object* v_macroScope_1793_; lean_object* v_traceMsgs_1794_; lean_object* v_expandedMacroDecls_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1807_; 
v_macroScope_1793_ = lean_ctor_get(v_a_1787_, 0);
v_traceMsgs_1794_ = lean_ctor_get(v_a_1787_, 1);
v_expandedMacroDecls_1795_ = lean_ctor_get(v_a_1787_, 2);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1797_ = v_a_1787_;
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_expandedMacroDecls_1795_);
lean_inc(v_traceMsgs_1794_);
lean_inc(v_macroScope_1793_);
lean_dec(v_a_1787_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_declName_1799_; lean_object* v___x_1801_; 
v_declName_1799_ = lean_ctor_get(v_toOLeanEntry_1743_, 1);
lean_inc(v_declName_1799_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 1);
lean_ctor_set(v___x_1789_, 1, v_expandedMacroDecls_1795_);
lean_ctor_set(v___x_1789_, 0, v_declName_1799_);
v___x_1801_ = v___x_1789_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_declName_1799_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_expandedMacroDecls_1795_);
v___x_1801_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 2, v___x_1801_);
v___x_1803_ = v___x_1797_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_macroScope_1793_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_traceMsgs_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; 
lean_inc_ref(v_toOLeanEntry_1743_);
v___x_1804_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1743_, v_a_1786_, v___x_1757_, v___y_1738_, v___x_1803_);
v___y_1774_ = v___x_1804_;
goto v___jp_1773_;
}
}
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v_a_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1809_);
v_a_1810_ = lean_ctor_get(v___x_1785_, 1);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1785_, 2);
v_a_1766_ = v_a_1809_;
v_a_1767_ = v_a_1810_;
goto v___jp_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1813_, lean_object* v_as_x27_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1813_, v_as_x27_1814_, v_b_1815_, v___y_1816_, v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v_as_x27_1814_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1819_, lean_object* v_stx_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_a_1829_; lean_object* v_fst_1830_; 
v___x_1823_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1820_);
v___x_1824_ = l_Lean_Syntax_getKind(v_stx_1820_);
v___x_1825_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1823_, v_env_1819_, v___x_1824_);
lean_dec(v___x_1824_);
v___x_1826_ = lean_box(0);
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1828_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1820_, v___x_1825_, v___x_1827_, v_a_1821_, v_a_1822_);
lean_dec(v___x_1825_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
v_fst_1830_ = lean_ctor_get(v_a_1829_, 0);
lean_inc(v_fst_1830_);
lean_dec(v_a_1829_);
if (lean_obj_tag(v_fst_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1828_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1828_, 0);
lean_dec(v_unused_1839_);
v___x_1833_ = v___x_1828_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1828_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1826_);
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_a_1840_ = lean_ctor_get(v___x_1828_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1828_, 0);
lean_dec(v_unused_1849_);
v___x_1842_ = v___x_1828_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1828_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_val_1844_; lean_object* v___x_1846_; 
v_val_1844_ = lean_ctor_get(v_fst_1830_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_fst_1830_, 1);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_val_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_val_1844_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_a_1840_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1850_, lean_object* v_stx_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1850_, v_stx_1851_, v_a_1852_, v_a_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1855_, lean_object* v_as_1856_, lean_object* v_as_x27_1857_, lean_object* v_b_1858_, lean_object* v_a_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1855_, v_as_x27_1857_, v_b_1858_, v___y_1860_, v___y_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1863_, lean_object* v_as_1864_, lean_object* v_as_x27_1865_, lean_object* v_b_1866_, lean_object* v_a_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1863_, v_as_1864_, v_as_x27_1865_, v_b_1866_, v_a_1867_, v___y_1868_, v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v_as_x27_1865_);
lean_dec(v_as_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1871_, lean_object* v_inst_1872_, lean_object* v_s_1873_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_apply_1(v_setNextMacroScope_1871_, v_s_1873_);
v___x_1875_ = lean_apply_2(v_inst_1872_, lean_box(0), v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_){
_start:
{
lean_object* v_getNextMacroScope_1879_; lean_object* v_setNextMacroScope_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v_getNextMacroScope_1879_ = lean_ctor_get(v_inst_1878_, 1);
v_setNextMacroScope_1880_ = lean_ctor_get(v_inst_1878_, 2);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_inst_1878_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_inst_1878_, 0);
lean_dec(v_unused_1890_);
v___x_1882_ = v_inst_1878_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_setNextMacroScope_1880_);
lean_inc(v_getNextMacroScope_1879_);
lean_dec(v_inst_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___f_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_inc(v_inst_1876_);
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1884_, 0, v_setNextMacroScope_1880_);
lean_closure_set(v___f_1884_, 1, v_inst_1876_);
v___x_1885_ = lean_apply_2(v_inst_1876_, lean_box(0), v_getNextMacroScope_1879_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 2, v___f_1884_);
lean_ctor_set(v___x_1882_, 1, v___x_1885_);
lean_ctor_set(v___x_1882_, 0, v_inst_1877_);
v___x_1887_ = v___x_1882_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_inst_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v___f_1884_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1891_, lean_object* v_n_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_){
_start:
{
lean_object* v_getNextMacroScope_1896_; lean_object* v_setNextMacroScope_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1906_; 
v_getNextMacroScope_1896_ = lean_ctor_get(v_inst_1895_, 1);
v_setNextMacroScope_1897_ = lean_ctor_get(v_inst_1895_, 2);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_inst_1895_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_inst_1895_, 0);
lean_dec(v_unused_1907_);
v___x_1899_ = v_inst_1895_;
v_isShared_1900_ = v_isSharedCheck_1906_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_setNextMacroScope_1897_);
lean_inc(v_getNextMacroScope_1896_);
lean_dec(v_inst_1895_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1906_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___f_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_inc(v_inst_1893_);
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1901_, 0, v_setNextMacroScope_1897_);
lean_closure_set(v___f_1901_, 1, v_inst_1893_);
v___x_1902_ = lean_apply_2(v_inst_1893_, lean_box(0), v_getNextMacroScope_1896_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 2, v___f_1901_);
lean_ctor_set(v___x_1899_, 1, v___x_1902_);
lean_ctor_set(v___x_1899_, 0, v_inst_1894_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_inst_1894_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___f_1901_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1908_, lean_object* v_snd_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_toMonadRef_1912_, lean_object* v_inst_1913_, lean_object* v_fst_1914_, uint8_t v_____do__lift_1915_){
_start:
{
if (v_____do__lift_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_fst_1914_);
lean_dec(v_inst_1913_);
lean_dec_ref(v_toMonadRef_1912_);
lean_dec_ref(v_inst_1911_);
lean_dec_ref(v_inst_1910_);
lean_dec_ref(v_snd_1909_);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_apply_2(v_toPure_1908_, lean_box(0), v___x_1916_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec(v_toPure_1908_);
v___x_1918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_snd_1909_);
v___x_1919_ = l_Lean_MessageData_ofFormat(v___x_1918_);
v___x_1920_ = l_Lean_addTrace___redArg(v_inst_1910_, v_inst_1911_, v_toMonadRef_1912_, v_inst_1913_, v_fst_1914_, v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1921_, lean_object* v_snd_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_toMonadRef_1925_, lean_object* v_inst_1926_, lean_object* v_fst_1927_, lean_object* v_____do__lift_1928_){
_start:
{
uint8_t v_____do__lift_1416__boxed_1929_; lean_object* v_res_1930_; 
v_____do__lift_1416__boxed_1929_ = lean_unbox(v_____do__lift_1928_);
v_res_1930_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1921_, v_snd_1922_, v_inst_1923_, v_inst_1924_, v_toMonadRef_1925_, v_inst_1926_, v_fst_1927_, v_____do__lift_1416__boxed_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1931_, lean_object* v_fst_1932_, lean_object* v_____do__lift_1933_, lean_object* v_____do__lift_1934_){
_start:
{
uint8_t v_hasTrace_1935_; 
v_hasTrace_1935_ = lean_ctor_get_uint8(v_____do__lift_1934_, sizeof(void*)*1);
if (v_hasTrace_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_fst_1932_);
v___x_1936_ = lean_box(v_hasTrace_1935_);
v___x_1937_ = lean_apply_2(v_toPure_1931_, lean_box(0), v___x_1936_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1939_ = l_Lean_Name_append(v___x_1938_, v_fst_1932_);
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1933_, v_____do__lift_1934_, v___x_1939_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(v___x_1940_);
v___x_1942_ = lean_apply_2(v_toPure_1931_, lean_box(0), v___x_1941_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(lean_object* v_toPure_1943_, lean_object* v_fst_1944_, lean_object* v_____do__lift_1945_, lean_object* v_____do__lift_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_liftMacroM___redArg___lam__1(v_toPure_1943_, v_fst_1944_, v_____do__lift_1945_, v_____do__lift_1946_);
lean_dec_ref(v_____do__lift_1946_);
lean_dec_ref(v_____do__lift_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1948_, lean_object* v_fst_1949_, lean_object* v_toBind_1950_, lean_object* v_inst_1951_, lean_object* v_____do__lift_1952_){
_start:
{
lean_object* v___f_1953_; lean_object* v___x_1954_; 
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1953_, 0, v_toPure_1948_);
lean_closure_set(v___f_1953_, 1, v_fst_1949_);
lean_closure_set(v___f_1953_, 2, v_____do__lift_1952_);
v___x_1954_ = lean_apply_4(v_toBind_1950_, lean_box(0), lean_box(0), v_inst_1951_, v___f_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1955_, lean_object* v_toPure_1956_, lean_object* v_inst_1957_, lean_object* v_toMonadRef_1958_, lean_object* v_inst_1959_, lean_object* v_toBind_1960_, lean_object* v_inst_1961_, lean_object* v_x_1962_){
_start:
{
lean_object* v_fst_1963_; lean_object* v_snd_1964_; lean_object* v_getInheritedTraceOptions_1965_; lean_object* v___f_1966_; lean_object* v___f_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_fst_1963_ = lean_ctor_get(v_x_1962_, 0);
lean_inc_n(v_fst_1963_, 2);
v_snd_1964_ = lean_ctor_get(v_x_1962_, 1);
lean_inc(v_snd_1964_);
lean_dec_ref(v_x_1962_);
v_getInheritedTraceOptions_1965_ = lean_ctor_get(v_inst_1955_, 2);
lean_inc(v_getInheritedTraceOptions_1965_);
lean_inc(v_toPure_1956_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1966_, 0, v_toPure_1956_);
lean_closure_set(v___f_1966_, 1, v_snd_1964_);
lean_closure_set(v___f_1966_, 2, v_inst_1957_);
lean_closure_set(v___f_1966_, 3, v_inst_1955_);
lean_closure_set(v___f_1966_, 4, v_toMonadRef_1958_);
lean_closure_set(v___f_1966_, 5, v_inst_1959_);
lean_closure_set(v___f_1966_, 6, v_fst_1963_);
lean_inc_n(v_toBind_1960_, 2);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1967_, 0, v_toPure_1956_);
lean_closure_set(v___f_1967_, 1, v_fst_1963_);
lean_closure_set(v___f_1967_, 2, v_toBind_1960_);
lean_closure_set(v___f_1967_, 3, v_inst_1961_);
v___x_1968_ = lean_apply_4(v_toBind_1960_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1965_, v___f_1967_);
v___x_1969_ = lean_apply_4(v_toBind_1960_, lean_box(0), lean_box(0), v___x_1968_, v___f_1966_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_1970_, lean_object* v___x_1971_, lean_object* v___x_1972_, lean_object* v_stx_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1970_, v_stx_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v___x_1972_);
lean_dec_ref(v___x_1971_);
v_a_1978_ = lean_ctor_get(v___x_1976_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1976_, 0);
lean_dec(v_unused_1987_);
v___x_1980_ = v___x_1976_;
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1976_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_box(0);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_a_1978_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2018_; 
v_val_1988_ = lean_ctor_get(v_a_1977_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1990_ = v_a_1977_;
v_isShared_1991_ = v_isSharedCheck_2018_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v_a_1977_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2018_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_snd_1992_; 
v_snd_1992_ = lean_ctor_get(v_val_1988_, 1);
lean_inc(v_snd_1992_);
lean_dec(v_val_1988_);
if (lean_obj_tag(v_snd_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
lean_del_object(v___x_1990_);
v_a_1993_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1976_, 2);
v_a_1994_ = lean_ctor_get(v_snd_1992_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_snd_1992_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1996_ = v_snd_1992_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v_snd_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_1195__overap_2000_; lean_object* v___x_2001_; 
v___x_1195__overap_2000_ = l_liftExcept___redArg(v___x_1971_, v___x_1972_, v___x_1999_);
lean_inc_ref(v___y_1974_);
v___x_2001_ = lean_apply_2(v___x_1195__overap_2000_, v___y_1974_, v_a_1993_);
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2017_; 
v_a_2004_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_1976_, 2);
v_a_2005_ = lean_ctor_get(v_snd_1992_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_snd_1992_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2007_ = v_snd_1992_;
v_isShared_2008_ = v_isSharedCheck_2017_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v_snd_1992_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2017_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v_a_2005_);
v___x_2010_ = v___x_1990_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_1199__overap_2013_; lean_object* v___x_2014_; 
v___x_1199__overap_2013_ = l_liftExcept___redArg(v___x_1971_, v___x_1972_, v___x_2012_);
lean_inc_ref(v___y_1974_);
v___x_2014_ = lean_apply_2(v___x_1199__overap_2013_, v___y_1974_, v_a_2004_);
return v___x_2014_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v___x_1972_);
lean_dec_ref(v___x_1971_);
v_a_2019_ = lean_ctor_get(v___x_1976_, 0);
v_a_2020_ = lean_ctor_get(v___x_1976_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1976_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_inc(v_a_2019_);
lean_dec(v___x_1976_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2019_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2028_, lean_object* v___x_2029_, lean_object* v___x_2030_, lean_object* v_stx_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2028_, v___x_2029_, v___x_2030_, v_stx_2031_, v___y_2032_, v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2035_, lean_object* v_declName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___x_2039_; lean_object* v_env_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2039_ = 0;
v_env_2040_ = l_Lean_Environment_setExporting(v_env_2035_, v___x_2039_);
lean_inc(v_declName_2036_);
v___x_2041_ = l_Lean_mkPrivateName(v_env_2040_, v_declName_2036_);
v___x_2042_ = 1;
lean_inc_ref(v_env_2040_);
v___x_2043_ = l_Lean_Environment_contains(v_env_2040_, v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_privateToUserName(v_declName_2036_);
v___x_2045_ = l_Lean_Environment_contains(v_env_2040_, v___x_2044_, v___x_2042_);
v___x_2046_ = lean_box(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v___y_2038_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref(v_env_2040_);
lean_dec(v_declName_2036_);
v___x_2048_ = lean_box(v___x_2043_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___y_2038_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2050_, lean_object* v_declName_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2050_, v_declName_2051_, v___y_2052_, v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2055_, lean_object* v_currNamespace_2056_, lean_object* v_openDecls_2057_, lean_object* v_n_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = l_Lean_ResolveName_resolveNamespace(v_env_2055_, v_currNamespace_2056_, v_openDecls_2057_, v_n_2058_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___y_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2063_, lean_object* v_currNamespace_2064_, lean_object* v_openDecls_2065_, lean_object* v_n_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2063_, v_currNamespace_2064_, v_openDecls_2065_, v_n_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2070_, lean_object* v_opts_2071_, lean_object* v_currNamespace_2072_, lean_object* v_openDecls_2073_, lean_object* v_n_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = l_Lean_ResolveName_resolveGlobalName(v_env_2070_, v_opts_2071_, v_currNamespace_2072_, v_openDecls_2073_, v_n_2074_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2079_, lean_object* v_opts_2080_, lean_object* v_currNamespace_2081_, lean_object* v_openDecls_2082_, lean_object* v_n_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2079_, v_opts_2080_, v_currNamespace_2081_, v_openDecls_2082_, v_n_2083_, v___y_2084_, v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v_opts_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2087_, lean_object* v_a_2088_, lean_object* v_____r_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_apply_2(v_toPure_2087_, lean_box(0), v_a_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2091_, lean_object* v_inst_2092_, lean_object* v___f_2093_, lean_object* v_toBind_2094_, lean_object* v___f_2095_, lean_object* v_____r_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = l_List_reverse___redArg(v_traceMsgs_2091_);
v___x_2098_ = l_List_forM___redArg(v_inst_2092_, v___x_2097_, v___f_2093_);
v___x_2099_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2098_, v___f_2095_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2100_, lean_object* v_macroScope_2101_, lean_object* v_toBind_2102_, lean_object* v___f_2103_, lean_object* v_____s_2104_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_apply_1(v_setNextMacroScope_2100_, v_macroScope_2101_);
v___x_2106_ = lean_apply_4(v_toBind_2102_, lean_box(0), lean_box(0), v___x_2105_, v___f_2103_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2107_, lean_object* v_toPure_2108_, lean_object* v_____r_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
v___x_2111_ = lean_apply_2(v_toPure_2108_, lean_box(0), v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_toMonadRef_2116_, lean_object* v_inst_2117_, lean_object* v_toBind_2118_, lean_object* v___f_2119_, lean_object* v_a_2120_, lean_object* v_x_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = 1;
v___x_2124_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2112_, v_inst_2113_, v_inst_2114_, v_inst_2115_, v_toMonadRef_2116_, v_inst_2117_, v_a_2120_, v___x_2123_);
v___x_2125_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v___x_2124_, v___f_2119_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2127_, lean_object* v_____do__lift_2128_, lean_object* v_____do__lift_2129_, lean_object* v_____do__lift_2130_, lean_object* v_____do__lift_2131_, lean_object* v_____do__lift_2132_, lean_object* v_x_2133_, lean_object* v_toPure_2134_, lean_object* v_inst_2135_, lean_object* v___f_2136_, lean_object* v_toBind_2137_, lean_object* v_setNextMacroScope_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_toMonadRef_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_toMonadExceptOf_2145_, lean_object* v_____do__lift_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2147_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2147_, 0, v_methods_2127_);
lean_ctor_set(v___x_2147_, 1, v_____do__lift_2128_);
lean_ctor_set(v___x_2147_, 2, v_____do__lift_2129_);
lean_ctor_set(v___x_2147_, 3, v_____do__lift_2130_);
lean_ctor_set(v___x_2147_, 4, v_____do__lift_2131_);
lean_ctor_set(v___x_2147_, 5, v_____do__lift_2132_);
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2149_, 0, v_____do__lift_2146_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
lean_ctor_set(v___x_2149_, 2, v___x_2148_);
v___x_2150_ = lean_apply_2(v_x_2133_, v___x_2147_, v___x_2149_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_a_2152_; lean_object* v_macroScope_2153_; lean_object* v_traceMsgs_2154_; lean_object* v_expandedMacroDecls_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v_toMonadExceptOf_2145_);
lean_dec_ref(v_inst_2144_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_a_2151_);
v_a_2152_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2150_, 2);
v_macroScope_2153_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_macroScope_2153_);
v_traceMsgs_2154_ = lean_ctor_get(v_a_2151_, 1);
lean_inc(v_traceMsgs_2154_);
v_expandedMacroDecls_2155_ = lean_ctor_get(v_a_2151_, 2);
lean_inc(v_expandedMacroDecls_2155_);
lean_dec(v_a_2151_);
lean_inc(v_toPure_2134_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2156_, 0, v_toPure_2134_);
lean_closure_set(v___f_2156_, 1, v_a_2152_);
lean_inc_n(v_toBind_2137_, 3);
lean_inc_ref_n(v_inst_2135_, 2);
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2157_, 0, v_traceMsgs_2154_);
lean_closure_set(v___f_2157_, 1, v_inst_2135_);
lean_closure_set(v___f_2157_, 2, v___f_2136_);
lean_closure_set(v___f_2157_, 3, v_toBind_2137_);
lean_closure_set(v___f_2157_, 4, v___f_2156_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2158_, 0, v_setNextMacroScope_2138_);
lean_closure_set(v___f_2158_, 1, v_macroScope_2153_);
lean_closure_set(v___f_2158_, 2, v_toBind_2137_);
lean_closure_set(v___f_2158_, 3, v___f_2157_);
v___x_2159_ = lean_box(0);
v___f_2160_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2160_, 0, v___x_2159_);
lean_closure_set(v___f_2160_, 1, v_toPure_2134_);
v___f_2161_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2161_, 0, v_inst_2135_);
lean_closure_set(v___f_2161_, 1, v_inst_2139_);
lean_closure_set(v___f_2161_, 2, v_inst_2140_);
lean_closure_set(v___f_2161_, 3, v_inst_2141_);
lean_closure_set(v___f_2161_, 4, v_toMonadRef_2142_);
lean_closure_set(v___f_2161_, 5, v_inst_2143_);
lean_closure_set(v___f_2161_, 6, v_toBind_2137_);
lean_closure_set(v___f_2161_, 7, v___f_2160_);
v___x_2162_ = l_List_forIn_x27_loop___redArg(v_inst_2135_, v___f_2161_, v_expandedMacroDecls_2155_, v___x_2159_);
lean_dec(v_expandedMacroDecls_2155_);
v___x_2163_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2162_, v___f_2158_);
return v___x_2163_;
}
else
{
lean_object* v_a_2164_; 
lean_dec(v_inst_2143_);
lean_dec_ref(v_toMonadRef_2142_);
lean_dec(v_inst_2141_);
lean_dec_ref(v_inst_2140_);
lean_dec_ref(v_inst_2139_);
lean_dec(v_setNextMacroScope_2138_);
lean_dec(v_toBind_2137_);
lean_dec(v___f_2136_);
lean_dec(v_toPure_2134_);
v_a_2164_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2150_, 2);
if (lean_obj_tag(v_a_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
lean_dec_ref(v_toMonadExceptOf_2145_);
v_a_2165_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_a_2165_);
v_a_2166_ = lean_ctor_get(v_a_2164_, 1);
lean_inc_ref(v_a_2166_);
lean_dec_ref_known(v_a_2164_, 2);
v___x_2167_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2168_ = lean_string_dec_eq(v_a_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_a_2166_);
v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
v___x_2171_ = l_Lean_throwErrorAt___redArg(v_inst_2135_, v_inst_2144_, v_a_2165_, v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
lean_dec_ref(v_a_2166_);
lean_dec_ref(v_inst_2135_);
v___x_2172_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2144_, v_a_2165_);
return v___x_2172_;
}
}
else
{
lean_object* v___x_2173_; 
lean_dec_ref(v_inst_2144_);
lean_dec_ref(v_inst_2135_);
v___x_2173_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2145_);
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2174_ = _args[0];
lean_object* v_____do__lift_2175_ = _args[1];
lean_object* v_____do__lift_2176_ = _args[2];
lean_object* v_____do__lift_2177_ = _args[3];
lean_object* v_____do__lift_2178_ = _args[4];
lean_object* v_____do__lift_2179_ = _args[5];
lean_object* v_x_2180_ = _args[6];
lean_object* v_toPure_2181_ = _args[7];
lean_object* v_inst_2182_ = _args[8];
lean_object* v___f_2183_ = _args[9];
lean_object* v_toBind_2184_ = _args[10];
lean_object* v_setNextMacroScope_2185_ = _args[11];
lean_object* v_inst_2186_ = _args[12];
lean_object* v_inst_2187_ = _args[13];
lean_object* v_inst_2188_ = _args[14];
lean_object* v_toMonadRef_2189_ = _args[15];
lean_object* v_inst_2190_ = _args[16];
lean_object* v_inst_2191_ = _args[17];
lean_object* v_toMonadExceptOf_2192_ = _args[18];
lean_object* v_____do__lift_2193_ = _args[19];
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2174_, v_____do__lift_2175_, v_____do__lift_2176_, v_____do__lift_2177_, v_____do__lift_2178_, v_____do__lift_2179_, v_x_2180_, v_toPure_2181_, v_inst_2182_, v___f_2183_, v_toBind_2184_, v_setNextMacroScope_2185_, v_inst_2186_, v_inst_2187_, v_inst_2188_, v_toMonadRef_2189_, v_inst_2190_, v_inst_2191_, v_toMonadExceptOf_2192_, v_____do__lift_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2195_, lean_object* v_____do__lift_2196_, lean_object* v_____do__lift_2197_, lean_object* v_____do__lift_2198_, lean_object* v_____do__lift_2199_, lean_object* v_x_2200_, lean_object* v_toPure_2201_, lean_object* v_inst_2202_, lean_object* v___f_2203_, lean_object* v_toBind_2204_, lean_object* v_setNextMacroScope_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_toMonadRef_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_toMonadExceptOf_2212_, lean_object* v_getNextMacroScope_2213_, lean_object* v_____do__lift_2214_){
_start:
{
lean_object* v___f_2215_; lean_object* v___x_2216_; 
lean_inc(v_toBind_2204_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2215_, 0, v_methods_2195_);
lean_closure_set(v___f_2215_, 1, v_____do__lift_2196_);
lean_closure_set(v___f_2215_, 2, v_____do__lift_2197_);
lean_closure_set(v___f_2215_, 3, v_____do__lift_2198_);
lean_closure_set(v___f_2215_, 4, v_____do__lift_2214_);
lean_closure_set(v___f_2215_, 5, v_____do__lift_2199_);
lean_closure_set(v___f_2215_, 6, v_x_2200_);
lean_closure_set(v___f_2215_, 7, v_toPure_2201_);
lean_closure_set(v___f_2215_, 8, v_inst_2202_);
lean_closure_set(v___f_2215_, 9, v___f_2203_);
lean_closure_set(v___f_2215_, 10, v_toBind_2204_);
lean_closure_set(v___f_2215_, 11, v_setNextMacroScope_2205_);
lean_closure_set(v___f_2215_, 12, v_inst_2206_);
lean_closure_set(v___f_2215_, 13, v_inst_2207_);
lean_closure_set(v___f_2215_, 14, v_inst_2208_);
lean_closure_set(v___f_2215_, 15, v_toMonadRef_2209_);
lean_closure_set(v___f_2215_, 16, v_inst_2210_);
lean_closure_set(v___f_2215_, 17, v_inst_2211_);
lean_closure_set(v___f_2215_, 18, v_toMonadExceptOf_2212_);
v___x_2216_ = lean_apply_4(v_toBind_2204_, lean_box(0), lean_box(0), v_getNextMacroScope_2213_, v___f_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2217_ = _args[0];
lean_object* v_____do__lift_2218_ = _args[1];
lean_object* v_____do__lift_2219_ = _args[2];
lean_object* v_____do__lift_2220_ = _args[3];
lean_object* v_____do__lift_2221_ = _args[4];
lean_object* v_x_2222_ = _args[5];
lean_object* v_toPure_2223_ = _args[6];
lean_object* v_inst_2224_ = _args[7];
lean_object* v___f_2225_ = _args[8];
lean_object* v_toBind_2226_ = _args[9];
lean_object* v_setNextMacroScope_2227_ = _args[10];
lean_object* v_inst_2228_ = _args[11];
lean_object* v_inst_2229_ = _args[12];
lean_object* v_inst_2230_ = _args[13];
lean_object* v_toMonadRef_2231_ = _args[14];
lean_object* v_inst_2232_ = _args[15];
lean_object* v_inst_2233_ = _args[16];
lean_object* v_toMonadExceptOf_2234_ = _args[17];
lean_object* v_getNextMacroScope_2235_ = _args[18];
lean_object* v_____do__lift_2236_ = _args[19];
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2217_, v_____do__lift_2218_, v_____do__lift_2219_, v_____do__lift_2220_, v_____do__lift_2221_, v_x_2222_, v_toPure_2223_, v_inst_2224_, v___f_2225_, v_toBind_2226_, v_setNextMacroScope_2227_, v_inst_2228_, v_inst_2229_, v_inst_2230_, v_toMonadRef_2231_, v_inst_2232_, v_inst_2233_, v_toMonadExceptOf_2234_, v_getNextMacroScope_2235_, v_____do__lift_2236_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2238_, lean_object* v_____do__lift_2239_, lean_object* v_____do__lift_2240_, lean_object* v_____do__lift_2241_, lean_object* v_x_2242_, lean_object* v_toPure_2243_, lean_object* v_inst_2244_, lean_object* v___f_2245_, lean_object* v_toBind_2246_, lean_object* v_setNextMacroScope_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_toMonadRef_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_toMonadExceptOf_2254_, lean_object* v_getNextMacroScope_2255_, lean_object* v_getMaxRecDepth_2256_, lean_object* v_____do__lift_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
lean_inc(v_toBind_2246_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2258_, 0, v_methods_2238_);
lean_closure_set(v___f_2258_, 1, v_____do__lift_2239_);
lean_closure_set(v___f_2258_, 2, v_____do__lift_2240_);
lean_closure_set(v___f_2258_, 3, v_____do__lift_2257_);
lean_closure_set(v___f_2258_, 4, v_____do__lift_2241_);
lean_closure_set(v___f_2258_, 5, v_x_2242_);
lean_closure_set(v___f_2258_, 6, v_toPure_2243_);
lean_closure_set(v___f_2258_, 7, v_inst_2244_);
lean_closure_set(v___f_2258_, 8, v___f_2245_);
lean_closure_set(v___f_2258_, 9, v_toBind_2246_);
lean_closure_set(v___f_2258_, 10, v_setNextMacroScope_2247_);
lean_closure_set(v___f_2258_, 11, v_inst_2248_);
lean_closure_set(v___f_2258_, 12, v_inst_2249_);
lean_closure_set(v___f_2258_, 13, v_inst_2250_);
lean_closure_set(v___f_2258_, 14, v_toMonadRef_2251_);
lean_closure_set(v___f_2258_, 15, v_inst_2252_);
lean_closure_set(v___f_2258_, 16, v_inst_2253_);
lean_closure_set(v___f_2258_, 17, v_toMonadExceptOf_2254_);
lean_closure_set(v___f_2258_, 18, v_getNextMacroScope_2255_);
v___x_2259_ = lean_apply_4(v_toBind_2246_, lean_box(0), lean_box(0), v_getMaxRecDepth_2256_, v___f_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2260_ = _args[0];
lean_object* v_____do__lift_2261_ = _args[1];
lean_object* v_____do__lift_2262_ = _args[2];
lean_object* v_____do__lift_2263_ = _args[3];
lean_object* v_x_2264_ = _args[4];
lean_object* v_toPure_2265_ = _args[5];
lean_object* v_inst_2266_ = _args[6];
lean_object* v___f_2267_ = _args[7];
lean_object* v_toBind_2268_ = _args[8];
lean_object* v_setNextMacroScope_2269_ = _args[9];
lean_object* v_inst_2270_ = _args[10];
lean_object* v_inst_2271_ = _args[11];
lean_object* v_inst_2272_ = _args[12];
lean_object* v_toMonadRef_2273_ = _args[13];
lean_object* v_inst_2274_ = _args[14];
lean_object* v_inst_2275_ = _args[15];
lean_object* v_toMonadExceptOf_2276_ = _args[16];
lean_object* v_getNextMacroScope_2277_ = _args[17];
lean_object* v_getMaxRecDepth_2278_ = _args[18];
lean_object* v_____do__lift_2279_ = _args[19];
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2260_, v_____do__lift_2261_, v_____do__lift_2262_, v_____do__lift_2263_, v_x_2264_, v_toPure_2265_, v_inst_2266_, v___f_2267_, v_toBind_2268_, v_setNextMacroScope_2269_, v_inst_2270_, v_inst_2271_, v_inst_2272_, v_toMonadRef_2273_, v_inst_2274_, v_inst_2275_, v_toMonadExceptOf_2276_, v_getNextMacroScope_2277_, v_getMaxRecDepth_2278_, v_____do__lift_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2281_, lean_object* v_methods_2282_, lean_object* v_____do__lift_2283_, lean_object* v_____do__lift_2284_, lean_object* v_x_2285_, lean_object* v_toPure_2286_, lean_object* v_inst_2287_, lean_object* v___f_2288_, lean_object* v_toBind_2289_, lean_object* v_setNextMacroScope_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_toMonadRef_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_toMonadExceptOf_2297_, lean_object* v_getNextMacroScope_2298_, lean_object* v_____do__lift_2299_){
_start:
{
lean_object* v_getRecDepth_2300_; lean_object* v_getMaxRecDepth_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; 
v_getRecDepth_2300_ = lean_ctor_get(v_inst_2281_, 1);
lean_inc(v_getRecDepth_2300_);
v_getMaxRecDepth_2301_ = lean_ctor_get(v_inst_2281_, 2);
lean_inc(v_getMaxRecDepth_2301_);
lean_dec_ref(v_inst_2281_);
lean_inc(v_toBind_2289_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2302_, 0, v_methods_2282_);
lean_closure_set(v___f_2302_, 1, v_____do__lift_2299_);
lean_closure_set(v___f_2302_, 2, v_____do__lift_2283_);
lean_closure_set(v___f_2302_, 3, v_____do__lift_2284_);
lean_closure_set(v___f_2302_, 4, v_x_2285_);
lean_closure_set(v___f_2302_, 5, v_toPure_2286_);
lean_closure_set(v___f_2302_, 6, v_inst_2287_);
lean_closure_set(v___f_2302_, 7, v___f_2288_);
lean_closure_set(v___f_2302_, 8, v_toBind_2289_);
lean_closure_set(v___f_2302_, 9, v_setNextMacroScope_2290_);
lean_closure_set(v___f_2302_, 10, v_inst_2291_);
lean_closure_set(v___f_2302_, 11, v_inst_2292_);
lean_closure_set(v___f_2302_, 12, v_inst_2293_);
lean_closure_set(v___f_2302_, 13, v_toMonadRef_2294_);
lean_closure_set(v___f_2302_, 14, v_inst_2295_);
lean_closure_set(v___f_2302_, 15, v_inst_2296_);
lean_closure_set(v___f_2302_, 16, v_toMonadExceptOf_2297_);
lean_closure_set(v___f_2302_, 17, v_getNextMacroScope_2298_);
lean_closure_set(v___f_2302_, 18, v_getMaxRecDepth_2301_);
v___x_2303_ = lean_apply_4(v_toBind_2289_, lean_box(0), lean_box(0), v_getRecDepth_2300_, v___f_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2304_ = _args[0];
lean_object* v_methods_2305_ = _args[1];
lean_object* v_____do__lift_2306_ = _args[2];
lean_object* v_____do__lift_2307_ = _args[3];
lean_object* v_x_2308_ = _args[4];
lean_object* v_toPure_2309_ = _args[5];
lean_object* v_inst_2310_ = _args[6];
lean_object* v___f_2311_ = _args[7];
lean_object* v_toBind_2312_ = _args[8];
lean_object* v_setNextMacroScope_2313_ = _args[9];
lean_object* v_inst_2314_ = _args[10];
lean_object* v_inst_2315_ = _args[11];
lean_object* v_inst_2316_ = _args[12];
lean_object* v_toMonadRef_2317_ = _args[13];
lean_object* v_inst_2318_ = _args[14];
lean_object* v_inst_2319_ = _args[15];
lean_object* v_toMonadExceptOf_2320_ = _args[16];
lean_object* v_getNextMacroScope_2321_ = _args[17];
lean_object* v_____do__lift_2322_ = _args[18];
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2304_, v_methods_2305_, v_____do__lift_2306_, v_____do__lift_2307_, v_x_2308_, v_toPure_2309_, v_inst_2310_, v___f_2311_, v_toBind_2312_, v_setNextMacroScope_2313_, v_inst_2314_, v_inst_2315_, v_inst_2316_, v_toMonadRef_2317_, v_inst_2318_, v_inst_2319_, v_toMonadExceptOf_2320_, v_getNextMacroScope_2321_, v_____do__lift_2322_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2324_, lean_object* v_methods_2325_, lean_object* v_____do__lift_2326_, lean_object* v_x_2327_, lean_object* v_toPure_2328_, lean_object* v_inst_2329_, lean_object* v___f_2330_, lean_object* v_toBind_2331_, lean_object* v_setNextMacroScope_2332_, lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_toMonadRef_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_toMonadExceptOf_2339_, lean_object* v_getNextMacroScope_2340_, lean_object* v_getContext_2341_, lean_object* v_____do__lift_2342_){
_start:
{
lean_object* v___f_2343_; lean_object* v___x_2344_; 
lean_inc(v_toBind_2331_);
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2343_, 0, v_inst_2324_);
lean_closure_set(v___f_2343_, 1, v_methods_2325_);
lean_closure_set(v___f_2343_, 2, v_____do__lift_2342_);
lean_closure_set(v___f_2343_, 3, v_____do__lift_2326_);
lean_closure_set(v___f_2343_, 4, v_x_2327_);
lean_closure_set(v___f_2343_, 5, v_toPure_2328_);
lean_closure_set(v___f_2343_, 6, v_inst_2329_);
lean_closure_set(v___f_2343_, 7, v___f_2330_);
lean_closure_set(v___f_2343_, 8, v_toBind_2331_);
lean_closure_set(v___f_2343_, 9, v_setNextMacroScope_2332_);
lean_closure_set(v___f_2343_, 10, v_inst_2333_);
lean_closure_set(v___f_2343_, 11, v_inst_2334_);
lean_closure_set(v___f_2343_, 12, v_inst_2335_);
lean_closure_set(v___f_2343_, 13, v_toMonadRef_2336_);
lean_closure_set(v___f_2343_, 14, v_inst_2337_);
lean_closure_set(v___f_2343_, 15, v_inst_2338_);
lean_closure_set(v___f_2343_, 16, v_toMonadExceptOf_2339_);
lean_closure_set(v___f_2343_, 17, v_getNextMacroScope_2340_);
v___x_2344_ = lean_apply_4(v_toBind_2331_, lean_box(0), lean_box(0), v_getContext_2341_, v___f_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2345_ = _args[0];
lean_object* v_methods_2346_ = _args[1];
lean_object* v_____do__lift_2347_ = _args[2];
lean_object* v_x_2348_ = _args[3];
lean_object* v_toPure_2349_ = _args[4];
lean_object* v_inst_2350_ = _args[5];
lean_object* v___f_2351_ = _args[6];
lean_object* v_toBind_2352_ = _args[7];
lean_object* v_setNextMacroScope_2353_ = _args[8];
lean_object* v_inst_2354_ = _args[9];
lean_object* v_inst_2355_ = _args[10];
lean_object* v_inst_2356_ = _args[11];
lean_object* v_toMonadRef_2357_ = _args[12];
lean_object* v_inst_2358_ = _args[13];
lean_object* v_inst_2359_ = _args[14];
lean_object* v_toMonadExceptOf_2360_ = _args[15];
lean_object* v_getNextMacroScope_2361_ = _args[16];
lean_object* v_getContext_2362_ = _args[17];
lean_object* v_____do__lift_2363_ = _args[18];
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2345_, v_methods_2346_, v_____do__lift_2347_, v_x_2348_, v_toPure_2349_, v_inst_2350_, v___f_2351_, v_toBind_2352_, v_setNextMacroScope_2353_, v_inst_2354_, v_inst_2355_, v_inst_2356_, v_toMonadRef_2357_, v_inst_2358_, v_inst_2359_, v_toMonadExceptOf_2360_, v_getNextMacroScope_2361_, v_getContext_2362_, v_____do__lift_2363_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2365_, lean_object* v_inst_2366_, lean_object* v_methods_2367_, lean_object* v_x_2368_, lean_object* v_toPure_2369_, lean_object* v_inst_2370_, lean_object* v___f_2371_, lean_object* v_toBind_2372_, lean_object* v_setNextMacroScope_2373_, lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_toMonadRef_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_toMonadExceptOf_2380_, lean_object* v_getNextMacroScope_2381_, lean_object* v_____do__lift_2382_){
_start:
{
lean_object* v_getCurrMacroScope_2383_; lean_object* v_getContext_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; 
v_getCurrMacroScope_2383_ = lean_ctor_get(v_toMonadQuotation_2365_, 1);
lean_inc(v_getCurrMacroScope_2383_);
v_getContext_2384_ = lean_ctor_get(v_toMonadQuotation_2365_, 2);
lean_inc(v_getContext_2384_);
lean_dec_ref(v_toMonadQuotation_2365_);
lean_inc(v_toBind_2372_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2385_, 0, v_inst_2366_);
lean_closure_set(v___f_2385_, 1, v_methods_2367_);
lean_closure_set(v___f_2385_, 2, v_____do__lift_2382_);
lean_closure_set(v___f_2385_, 3, v_x_2368_);
lean_closure_set(v___f_2385_, 4, v_toPure_2369_);
lean_closure_set(v___f_2385_, 5, v_inst_2370_);
lean_closure_set(v___f_2385_, 6, v___f_2371_);
lean_closure_set(v___f_2385_, 7, v_toBind_2372_);
lean_closure_set(v___f_2385_, 8, v_setNextMacroScope_2373_);
lean_closure_set(v___f_2385_, 9, v_inst_2374_);
lean_closure_set(v___f_2385_, 10, v_inst_2375_);
lean_closure_set(v___f_2385_, 11, v_inst_2376_);
lean_closure_set(v___f_2385_, 12, v_toMonadRef_2377_);
lean_closure_set(v___f_2385_, 13, v_inst_2378_);
lean_closure_set(v___f_2385_, 14, v_inst_2379_);
lean_closure_set(v___f_2385_, 15, v_toMonadExceptOf_2380_);
lean_closure_set(v___f_2385_, 16, v_getNextMacroScope_2381_);
lean_closure_set(v___f_2385_, 17, v_getContext_2384_);
v___x_2386_ = lean_apply_4(v_toBind_2372_, lean_box(0), lean_box(0), v_getCurrMacroScope_2383_, v___f_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2387_ = _args[0];
lean_object* v_inst_2388_ = _args[1];
lean_object* v_methods_2389_ = _args[2];
lean_object* v_x_2390_ = _args[3];
lean_object* v_toPure_2391_ = _args[4];
lean_object* v_inst_2392_ = _args[5];
lean_object* v___f_2393_ = _args[6];
lean_object* v_toBind_2394_ = _args[7];
lean_object* v_setNextMacroScope_2395_ = _args[8];
lean_object* v_inst_2396_ = _args[9];
lean_object* v_inst_2397_ = _args[10];
lean_object* v_inst_2398_ = _args[11];
lean_object* v_toMonadRef_2399_ = _args[12];
lean_object* v_inst_2400_ = _args[13];
lean_object* v_inst_2401_ = _args[14];
lean_object* v_toMonadExceptOf_2402_ = _args[15];
lean_object* v_getNextMacroScope_2403_ = _args[16];
lean_object* v_____do__lift_2404_ = _args[17];
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2387_, v_inst_2388_, v_methods_2389_, v_x_2390_, v_toPure_2391_, v_inst_2392_, v___f_2393_, v_toBind_2394_, v_setNextMacroScope_2395_, v_inst_2396_, v_inst_2397_, v_inst_2398_, v_toMonadRef_2399_, v_inst_2400_, v_inst_2401_, v_toMonadExceptOf_2402_, v_getNextMacroScope_2403_, v_____do__lift_2404_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2406_, lean_object* v_env_2407_, lean_object* v_currNamespace_2408_, lean_object* v_opts_2409_, lean_object* v___x_2410_, lean_object* v___f_2411_, lean_object* v___f_2412_, lean_object* v_toMonadQuotation_2413_, lean_object* v_inst_2414_, lean_object* v_x_2415_, lean_object* v_toPure_2416_, lean_object* v_inst_2417_, lean_object* v___f_2418_, lean_object* v_toBind_2419_, lean_object* v_setNextMacroScope_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_toMonadExceptOf_2426_, lean_object* v_getNextMacroScope_2427_, lean_object* v_openDecls_2428_){
_start:
{
lean_object* v_getRef_2429_; lean_object* v___f_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v_methods_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; 
v_getRef_2429_ = lean_ctor_get(v_toMonadRef_2406_, 0);
lean_inc(v_getRef_2429_);
lean_inc(v_openDecls_2428_);
lean_inc_n(v_currNamespace_2408_, 2);
lean_inc_ref(v_env_2407_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2430_, 0, v_env_2407_);
lean_closure_set(v___f_2430_, 1, v_currNamespace_2408_);
lean_closure_set(v___f_2430_, 2, v_openDecls_2428_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2431_, 0, v_env_2407_);
lean_closure_set(v___f_2431_, 1, v_opts_2409_);
lean_closure_set(v___f_2431_, 2, v_currNamespace_2408_);
lean_closure_set(v___f_2431_, 3, v_openDecls_2428_);
v___x_2432_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2432_, 0, lean_box(0));
lean_closure_set(v___x_2432_, 1, lean_box(0));
lean_closure_set(v___x_2432_, 2, v___x_2410_);
lean_closure_set(v___x_2432_, 3, lean_box(0));
lean_closure_set(v___x_2432_, 4, v_currNamespace_2408_);
v_methods_2433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2433_, 0, v___f_2411_);
lean_ctor_set(v_methods_2433_, 1, v___x_2432_);
lean_ctor_set(v_methods_2433_, 2, v___f_2412_);
lean_ctor_set(v_methods_2433_, 3, v___f_2430_);
lean_ctor_set(v_methods_2433_, 4, v___f_2431_);
lean_inc(v_toBind_2419_);
v___f_2434_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2434_, 0, v_toMonadQuotation_2413_);
lean_closure_set(v___f_2434_, 1, v_inst_2414_);
lean_closure_set(v___f_2434_, 2, v_methods_2433_);
lean_closure_set(v___f_2434_, 3, v_x_2415_);
lean_closure_set(v___f_2434_, 4, v_toPure_2416_);
lean_closure_set(v___f_2434_, 5, v_inst_2417_);
lean_closure_set(v___f_2434_, 6, v___f_2418_);
lean_closure_set(v___f_2434_, 7, v_toBind_2419_);
lean_closure_set(v___f_2434_, 8, v_setNextMacroScope_2420_);
lean_closure_set(v___f_2434_, 9, v_inst_2421_);
lean_closure_set(v___f_2434_, 10, v_inst_2422_);
lean_closure_set(v___f_2434_, 11, v_inst_2423_);
lean_closure_set(v___f_2434_, 12, v_toMonadRef_2406_);
lean_closure_set(v___f_2434_, 13, v_inst_2424_);
lean_closure_set(v___f_2434_, 14, v_inst_2425_);
lean_closure_set(v___f_2434_, 15, v_toMonadExceptOf_2426_);
lean_closure_set(v___f_2434_, 16, v_getNextMacroScope_2427_);
v___x_2435_ = lean_apply_4(v_toBind_2419_, lean_box(0), lean_box(0), v_getRef_2429_, v___f_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2436_ = _args[0];
lean_object* v_env_2437_ = _args[1];
lean_object* v_currNamespace_2438_ = _args[2];
lean_object* v_opts_2439_ = _args[3];
lean_object* v___x_2440_ = _args[4];
lean_object* v___f_2441_ = _args[5];
lean_object* v___f_2442_ = _args[6];
lean_object* v_toMonadQuotation_2443_ = _args[7];
lean_object* v_inst_2444_ = _args[8];
lean_object* v_x_2445_ = _args[9];
lean_object* v_toPure_2446_ = _args[10];
lean_object* v_inst_2447_ = _args[11];
lean_object* v___f_2448_ = _args[12];
lean_object* v_toBind_2449_ = _args[13];
lean_object* v_setNextMacroScope_2450_ = _args[14];
lean_object* v_inst_2451_ = _args[15];
lean_object* v_inst_2452_ = _args[16];
lean_object* v_inst_2453_ = _args[17];
lean_object* v_inst_2454_ = _args[18];
lean_object* v_inst_2455_ = _args[19];
lean_object* v_toMonadExceptOf_2456_ = _args[20];
lean_object* v_getNextMacroScope_2457_ = _args[21];
lean_object* v_openDecls_2458_ = _args[22];
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2436_, v_env_2437_, v_currNamespace_2438_, v_opts_2439_, v___x_2440_, v___f_2441_, v___f_2442_, v_toMonadQuotation_2443_, v_inst_2444_, v_x_2445_, v_toPure_2446_, v_inst_2447_, v___f_2448_, v_toBind_2449_, v_setNextMacroScope_2450_, v_inst_2451_, v_inst_2452_, v_inst_2453_, v_inst_2454_, v_inst_2455_, v_toMonadExceptOf_2456_, v_getNextMacroScope_2457_, v_openDecls_2458_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2460_, lean_object* v_env_2461_, lean_object* v_opts_2462_, lean_object* v___x_2463_, lean_object* v___f_2464_, lean_object* v___f_2465_, lean_object* v_toMonadQuotation_2466_, lean_object* v_inst_2467_, lean_object* v_x_2468_, lean_object* v_toPure_2469_, lean_object* v_inst_2470_, lean_object* v___f_2471_, lean_object* v_toBind_2472_, lean_object* v_setNextMacroScope_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_toMonadExceptOf_2479_, lean_object* v_getNextMacroScope_2480_, lean_object* v_getOpenDecls_2481_, lean_object* v_currNamespace_2482_){
_start:
{
lean_object* v___f_2483_; lean_object* v___x_2484_; 
lean_inc(v_toBind_2472_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2483_, 0, v_toMonadRef_2460_);
lean_closure_set(v___f_2483_, 1, v_env_2461_);
lean_closure_set(v___f_2483_, 2, v_currNamespace_2482_);
lean_closure_set(v___f_2483_, 3, v_opts_2462_);
lean_closure_set(v___f_2483_, 4, v___x_2463_);
lean_closure_set(v___f_2483_, 5, v___f_2464_);
lean_closure_set(v___f_2483_, 6, v___f_2465_);
lean_closure_set(v___f_2483_, 7, v_toMonadQuotation_2466_);
lean_closure_set(v___f_2483_, 8, v_inst_2467_);
lean_closure_set(v___f_2483_, 9, v_x_2468_);
lean_closure_set(v___f_2483_, 10, v_toPure_2469_);
lean_closure_set(v___f_2483_, 11, v_inst_2470_);
lean_closure_set(v___f_2483_, 12, v___f_2471_);
lean_closure_set(v___f_2483_, 13, v_toBind_2472_);
lean_closure_set(v___f_2483_, 14, v_setNextMacroScope_2473_);
lean_closure_set(v___f_2483_, 15, v_inst_2474_);
lean_closure_set(v___f_2483_, 16, v_inst_2475_);
lean_closure_set(v___f_2483_, 17, v_inst_2476_);
lean_closure_set(v___f_2483_, 18, v_inst_2477_);
lean_closure_set(v___f_2483_, 19, v_inst_2478_);
lean_closure_set(v___f_2483_, 20, v_toMonadExceptOf_2479_);
lean_closure_set(v___f_2483_, 21, v_getNextMacroScope_2480_);
v___x_2484_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v_getOpenDecls_2481_, v___f_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2485_ = _args[0];
lean_object* v_env_2486_ = _args[1];
lean_object* v_opts_2487_ = _args[2];
lean_object* v___x_2488_ = _args[3];
lean_object* v___f_2489_ = _args[4];
lean_object* v___f_2490_ = _args[5];
lean_object* v_toMonadQuotation_2491_ = _args[6];
lean_object* v_inst_2492_ = _args[7];
lean_object* v_x_2493_ = _args[8];
lean_object* v_toPure_2494_ = _args[9];
lean_object* v_inst_2495_ = _args[10];
lean_object* v___f_2496_ = _args[11];
lean_object* v_toBind_2497_ = _args[12];
lean_object* v_setNextMacroScope_2498_ = _args[13];
lean_object* v_inst_2499_ = _args[14];
lean_object* v_inst_2500_ = _args[15];
lean_object* v_inst_2501_ = _args[16];
lean_object* v_inst_2502_ = _args[17];
lean_object* v_inst_2503_ = _args[18];
lean_object* v_toMonadExceptOf_2504_ = _args[19];
lean_object* v_getNextMacroScope_2505_ = _args[20];
lean_object* v_getOpenDecls_2506_ = _args[21];
lean_object* v_currNamespace_2507_ = _args[22];
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2485_, v_env_2486_, v_opts_2487_, v___x_2488_, v___f_2489_, v___f_2490_, v_toMonadQuotation_2491_, v_inst_2492_, v_x_2493_, v_toPure_2494_, v_inst_2495_, v___f_2496_, v_toBind_2497_, v_setNextMacroScope_2498_, v_inst_2499_, v_inst_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_toMonadExceptOf_2504_, v_getNextMacroScope_2505_, v_getOpenDecls_2506_, v_currNamespace_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2509_, lean_object* v_toMonadRef_2510_, lean_object* v_env_2511_, lean_object* v___x_2512_, lean_object* v___f_2513_, lean_object* v___f_2514_, lean_object* v_toMonadQuotation_2515_, lean_object* v_inst_2516_, lean_object* v_x_2517_, lean_object* v_toPure_2518_, lean_object* v_inst_2519_, lean_object* v___f_2520_, lean_object* v_toBind_2521_, lean_object* v_setNextMacroScope_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_toMonadExceptOf_2528_, lean_object* v_getNextMacroScope_2529_, lean_object* v_opts_2530_){
_start:
{
lean_object* v_getCurrNamespace_2531_; lean_object* v_getOpenDecls_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; 
v_getCurrNamespace_2531_ = lean_ctor_get(v_inst_2509_, 0);
lean_inc(v_getCurrNamespace_2531_);
v_getOpenDecls_2532_ = lean_ctor_get(v_inst_2509_, 1);
lean_inc(v_getOpenDecls_2532_);
lean_dec_ref(v_inst_2509_);
lean_inc(v_toBind_2521_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2533_, 0, v_toMonadRef_2510_);
lean_closure_set(v___f_2533_, 1, v_env_2511_);
lean_closure_set(v___f_2533_, 2, v_opts_2530_);
lean_closure_set(v___f_2533_, 3, v___x_2512_);
lean_closure_set(v___f_2533_, 4, v___f_2513_);
lean_closure_set(v___f_2533_, 5, v___f_2514_);
lean_closure_set(v___f_2533_, 6, v_toMonadQuotation_2515_);
lean_closure_set(v___f_2533_, 7, v_inst_2516_);
lean_closure_set(v___f_2533_, 8, v_x_2517_);
lean_closure_set(v___f_2533_, 9, v_toPure_2518_);
lean_closure_set(v___f_2533_, 10, v_inst_2519_);
lean_closure_set(v___f_2533_, 11, v___f_2520_);
lean_closure_set(v___f_2533_, 12, v_toBind_2521_);
lean_closure_set(v___f_2533_, 13, v_setNextMacroScope_2522_);
lean_closure_set(v___f_2533_, 14, v_inst_2523_);
lean_closure_set(v___f_2533_, 15, v_inst_2524_);
lean_closure_set(v___f_2533_, 16, v_inst_2525_);
lean_closure_set(v___f_2533_, 17, v_inst_2526_);
lean_closure_set(v___f_2533_, 18, v_inst_2527_);
lean_closure_set(v___f_2533_, 19, v_toMonadExceptOf_2528_);
lean_closure_set(v___f_2533_, 20, v_getNextMacroScope_2529_);
lean_closure_set(v___f_2533_, 21, v_getOpenDecls_2532_);
v___x_2534_ = lean_apply_4(v_toBind_2521_, lean_box(0), lean_box(0), v_getCurrNamespace_2531_, v___f_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2535_ = _args[0];
lean_object* v_toMonadRef_2536_ = _args[1];
lean_object* v_env_2537_ = _args[2];
lean_object* v___x_2538_ = _args[3];
lean_object* v___f_2539_ = _args[4];
lean_object* v___f_2540_ = _args[5];
lean_object* v_toMonadQuotation_2541_ = _args[6];
lean_object* v_inst_2542_ = _args[7];
lean_object* v_x_2543_ = _args[8];
lean_object* v_toPure_2544_ = _args[9];
lean_object* v_inst_2545_ = _args[10];
lean_object* v___f_2546_ = _args[11];
lean_object* v_toBind_2547_ = _args[12];
lean_object* v_setNextMacroScope_2548_ = _args[13];
lean_object* v_inst_2549_ = _args[14];
lean_object* v_inst_2550_ = _args[15];
lean_object* v_inst_2551_ = _args[16];
lean_object* v_inst_2552_ = _args[17];
lean_object* v_inst_2553_ = _args[18];
lean_object* v_toMonadExceptOf_2554_ = _args[19];
lean_object* v_getNextMacroScope_2555_ = _args[20];
lean_object* v_opts_2556_ = _args[21];
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2535_, v_toMonadRef_2536_, v_env_2537_, v___x_2538_, v___f_2539_, v___f_2540_, v_toMonadQuotation_2541_, v_inst_2542_, v_x_2543_, v_toPure_2544_, v_inst_2545_, v___f_2546_, v_toBind_2547_, v_setNextMacroScope_2548_, v_inst_2549_, v_inst_2550_, v_inst_2551_, v_inst_2552_, v_inst_2553_, v_toMonadExceptOf_2554_, v_getNextMacroScope_2555_, v_opts_2556_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v___x_2558_, lean_object* v___x_2559_, lean_object* v_inst_2560_, lean_object* v_toMonadRef_2561_, lean_object* v___x_2562_, lean_object* v_toMonadQuotation_2563_, lean_object* v_inst_2564_, lean_object* v_x_2565_, lean_object* v_toPure_2566_, lean_object* v_inst_2567_, lean_object* v___f_2568_, lean_object* v_toBind_2569_, lean_object* v_setNextMacroScope_2570_, lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_toMonadExceptOf_2576_, lean_object* v_getNextMacroScope_2577_, lean_object* v_env_2578_){
_start:
{
lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; 
lean_inc_ref_n(v_env_2578_, 2);
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2579_, 0, v_env_2578_);
lean_closure_set(v___f_2579_, 1, v___x_2558_);
lean_closure_set(v___f_2579_, 2, v___x_2559_);
v___f_2580_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2580_, 0, v_env_2578_);
lean_inc(v_inst_2573_);
lean_inc(v_toBind_2569_);
v___f_2581_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2581_, 0, v_inst_2560_);
lean_closure_set(v___f_2581_, 1, v_toMonadRef_2561_);
lean_closure_set(v___f_2581_, 2, v_env_2578_);
lean_closure_set(v___f_2581_, 3, v___x_2562_);
lean_closure_set(v___f_2581_, 4, v___f_2579_);
lean_closure_set(v___f_2581_, 5, v___f_2580_);
lean_closure_set(v___f_2581_, 6, v_toMonadQuotation_2563_);
lean_closure_set(v___f_2581_, 7, v_inst_2564_);
lean_closure_set(v___f_2581_, 8, v_x_2565_);
lean_closure_set(v___f_2581_, 9, v_toPure_2566_);
lean_closure_set(v___f_2581_, 10, v_inst_2567_);
lean_closure_set(v___f_2581_, 11, v___f_2568_);
lean_closure_set(v___f_2581_, 12, v_toBind_2569_);
lean_closure_set(v___f_2581_, 13, v_setNextMacroScope_2570_);
lean_closure_set(v___f_2581_, 14, v_inst_2571_);
lean_closure_set(v___f_2581_, 15, v_inst_2572_);
lean_closure_set(v___f_2581_, 16, v_inst_2573_);
lean_closure_set(v___f_2581_, 17, v_inst_2574_);
lean_closure_set(v___f_2581_, 18, v_inst_2575_);
lean_closure_set(v___f_2581_, 19, v_toMonadExceptOf_2576_);
lean_closure_set(v___f_2581_, 20, v_getNextMacroScope_2577_);
v___x_2582_ = lean_apply_4(v_toBind_2569_, lean_box(0), lean_box(0), v_inst_2573_, v___f_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_2583_ = _args[0];
lean_object* v___x_2584_ = _args[1];
lean_object* v_inst_2585_ = _args[2];
lean_object* v_toMonadRef_2586_ = _args[3];
lean_object* v___x_2587_ = _args[4];
lean_object* v_toMonadQuotation_2588_ = _args[5];
lean_object* v_inst_2589_ = _args[6];
lean_object* v_x_2590_ = _args[7];
lean_object* v_toPure_2591_ = _args[8];
lean_object* v_inst_2592_ = _args[9];
lean_object* v___f_2593_ = _args[10];
lean_object* v_toBind_2594_ = _args[11];
lean_object* v_setNextMacroScope_2595_ = _args[12];
lean_object* v_inst_2596_ = _args[13];
lean_object* v_inst_2597_ = _args[14];
lean_object* v_inst_2598_ = _args[15];
lean_object* v_inst_2599_ = _args[16];
lean_object* v_inst_2600_ = _args[17];
lean_object* v_toMonadExceptOf_2601_ = _args[18];
lean_object* v_getNextMacroScope_2602_ = _args[19];
lean_object* v_env_2603_ = _args[20];
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v___x_2583_, v___x_2584_, v_inst_2585_, v_toMonadRef_2586_, v___x_2587_, v_toMonadQuotation_2588_, v_inst_2589_, v_x_2590_, v_toPure_2591_, v_inst_2592_, v___f_2593_, v_toBind_2594_, v_setNextMacroScope_2595_, v_inst_2596_, v_inst_2597_, v_inst_2598_, v_inst_2599_, v_inst_2600_, v_toMonadExceptOf_2601_, v_getNextMacroScope_2602_, v_env_2603_);
return v_res_2604_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_EStateM_nonBacktrackable(lean_box(0));
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2626_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___f_2628_; 
v___x_2627_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2628_, 0, v___x_2627_);
return v___f_2628_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___f_2630_; 
v___x_2629_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2630_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2630_, 0, v___x_2629_);
return v___f_2630_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; 
v___f_2631_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2632_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___f_2632_);
lean_ctor_set(v___x_2633_, 1, v___f_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_inst_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_toApplicative_2648_; lean_object* v_toBind_2649_; lean_object* v_getEnv_2650_; lean_object* v_toMonadExceptOf_2651_; lean_object* v_toMonadRef_2652_; lean_object* v_toMonadQuotation_2653_; lean_object* v_getNextMacroScope_2654_; lean_object* v_setNextMacroScope_2655_; lean_object* v_toPure_2656_; lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; 
v___x_2646_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2647_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2648_ = lean_ctor_get(v_inst_2636_, 0);
v_toBind_2649_ = lean_ctor_get(v_inst_2636_, 1);
lean_inc_n(v_toBind_2649_, 3);
v_getEnv_2650_ = lean_ctor_get(v_inst_2638_, 0);
lean_inc(v_getEnv_2650_);
v_toMonadExceptOf_2651_ = lean_ctor_get(v_inst_2640_, 0);
lean_inc_ref(v_toMonadExceptOf_2651_);
v_toMonadRef_2652_ = lean_ctor_get(v_inst_2640_, 1);
lean_inc_ref_n(v_toMonadRef_2652_, 2);
v_toMonadQuotation_2653_ = lean_ctor_get(v_inst_2637_, 0);
lean_inc_ref(v_toMonadQuotation_2653_);
v_getNextMacroScope_2654_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc(v_getNextMacroScope_2654_);
v_setNextMacroScope_2655_ = lean_ctor_get(v_inst_2637_, 2);
lean_inc(v_setNextMacroScope_2655_);
lean_dec_ref(v_inst_2637_);
v_toPure_2656_ = lean_ctor_get(v_toApplicative_2648_, 1);
lean_inc_n(v_toPure_2656_, 2);
v___x_2657_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2643_);
lean_inc(v_inst_2644_);
lean_inc_ref(v_inst_2636_);
lean_inc_ref(v_inst_2642_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2658_, 0, v_inst_2642_);
lean_closure_set(v___f_2658_, 1, v_toPure_2656_);
lean_closure_set(v___f_2658_, 2, v_inst_2636_);
lean_closure_set(v___f_2658_, 3, v_toMonadRef_2652_);
lean_closure_set(v___f_2658_, 4, v_inst_2644_);
lean_closure_set(v___f_2658_, 5, v_toBind_2649_);
lean_closure_set(v___f_2658_, 6, v_inst_2643_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2659_, 0, v___x_2647_);
lean_closure_set(v___f_2659_, 1, v___x_2657_);
lean_closure_set(v___f_2659_, 2, v_inst_2641_);
lean_closure_set(v___f_2659_, 3, v_toMonadRef_2652_);
lean_closure_set(v___f_2659_, 4, v___x_2646_);
lean_closure_set(v___f_2659_, 5, v_toMonadQuotation_2653_);
lean_closure_set(v___f_2659_, 6, v_inst_2639_);
lean_closure_set(v___f_2659_, 7, v_x_2645_);
lean_closure_set(v___f_2659_, 8, v_toPure_2656_);
lean_closure_set(v___f_2659_, 9, v_inst_2636_);
lean_closure_set(v___f_2659_, 10, v___f_2658_);
lean_closure_set(v___f_2659_, 11, v_toBind_2649_);
lean_closure_set(v___f_2659_, 12, v_setNextMacroScope_2655_);
lean_closure_set(v___f_2659_, 13, v_inst_2638_);
lean_closure_set(v___f_2659_, 14, v_inst_2642_);
lean_closure_set(v___f_2659_, 15, v_inst_2643_);
lean_closure_set(v___f_2659_, 16, v_inst_2644_);
lean_closure_set(v___f_2659_, 17, v_inst_2640_);
lean_closure_set(v___f_2659_, 18, v_toMonadExceptOf_2651_);
lean_closure_set(v___f_2659_, 19, v_getNextMacroScope_2654_);
v___x_2660_ = lean_apply_4(v_toBind_2649_, lean_box(0), lean_box(0), v_getEnv_2650_, v___f_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2661_, lean_object* v_00_u03b1_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_x_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_inst_2670_, v_inst_2671_, v_x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2675_, lean_object* v_00_u03b1_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_x_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Elab_liftMacroM(v_m_2675_, v_00_u03b1_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_inst_2684_, v_inst_2685_, v_inst_2686_, v_x_2687_);
lean_dec(v_inst_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_x_2698_, lean_object* v_stx_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_apply_1(v_x_2698_, v_stx_2699_);
v___x_2701_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_x_2713_, lean_object* v_stx_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_apply_1(v_x_2713_, v_stx_2714_);
v___x_2716_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_x_2728_, lean_object* v_stx_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Elab_adaptMacro(v_m_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_inst_2725_, v_inst_2726_, v_inst_2727_, v_x_2728_, v_stx_2729_);
lean_dec(v_inst_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2731_, lean_object* v_currNamespace_2732_, lean_object* v_idx_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_name_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_inc(v_idx_2733_);
lean_inc(v_baseName_2731_);
v_name_2736_ = lean_name_append_index_after(v_baseName_2731_, v_idx_2733_);
lean_inc(v_name_2736_);
lean_inc(v_currNamespace_2732_);
v___x_2737_ = l_Lean_Name_append(v_currNamespace_2732_, v_name_2736_);
v___x_2738_ = l_Lean_Macro_hasDecl(v___x_2737_, v_a_2734_, v_a_2735_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; uint8_t v___x_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
v___x_2740_ = lean_unbox(v_a_2739_);
lean_dec(v_a_2739_);
if (v___x_2740_ == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_idx_2733_);
lean_dec(v_currNamespace_2732_);
lean_dec(v_baseName_2731_);
v_a_2741_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2738_, 0);
lean_dec(v_unused_2749_);
v___x_2743_ = v___x_2738_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2738_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_name_2736_);
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_name_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v_name_2736_);
v_a_2750_ = lean_ctor_get(v___x_2738_, 1);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2738_, 2);
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = lean_nat_add(v_idx_2733_, v___x_2751_);
lean_dec(v_idx_2733_);
v_idx_2733_ = v___x_2752_;
v_a_2735_ = v_a_2750_;
goto _start;
}
}
else
{
lean_object* v_a_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_name_2736_);
lean_dec(v_idx_2733_);
lean_dec(v_currNamespace_2732_);
lean_dec(v_baseName_2731_);
v_a_2754_ = lean_ctor_get(v___x_2738_, 0);
v_a_2755_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2738_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_inc(v_a_2754_);
lean_dec(v___x_2738_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2763_, lean_object* v_currNamespace_2764_, lean_object* v_idx_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2763_, v_currNamespace_2764_, v_idx_2765_, v_a_2766_, v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Macro_getCurrNamespace(v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc_n(v_a_2773_, 2);
v_a_2774_ = lean_ctor_get(v___x_2772_, 1);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2772_, 2);
lean_inc(v_baseName_2769_);
v___x_2775_ = l_Lean_Name_append(v_a_2773_, v_baseName_2769_);
v___x_2776_ = l_Lean_Macro_hasDecl(v___x_2775_, v_a_2770_, v_a_2774_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
v___x_2778_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
if (v___x_2778_ == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2773_);
v_a_2779_ = lean_ctor_get(v___x_2776_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2776_, 0);
lean_dec(v_unused_2787_);
v___x_2781_ = v___x_2776_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2776_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_baseName_2769_);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_baseName_2769_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v___x_2776_, 1);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2776_, 2);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2769_, v_a_2773_, v___x_2789_, v_a_2770_, v_a_2788_);
return v___x_2790_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2773_);
lean_dec(v_baseName_2769_);
v_a_2791_ = lean_ctor_get(v___x_2776_, 0);
v_a_2792_ = lean_ctor_get(v___x_2776_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2776_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_inc(v_a_2791_);
lean_dec(v___x_2776_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2791_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_dec(v_baseName_2769_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2800_, v_a_2801_, v_a_2802_);
lean_dec_ref(v_a_2801_);
return v_res_2803_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2806_ = l_Lean_stringToMessageData(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_inst_2810_, lean_object* v_name_2811_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2812_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2813_ = l_Lean_MessageData_ofName(v_name_2811_);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Lean_logError___redArg(v_inst_2807_, v_inst_2808_, v_inst_2809_, v_inst_2810_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_ex_2821_){
_start:
{
if (lean_obj_tag(v_ex_2821_) == 0)
{
lean_object* v_ref_2822_; lean_object* v_msg_2823_; lean_object* v___x_2824_; 
lean_dec(v_inst_2820_);
v_ref_2822_ = lean_ctor_get(v_ex_2821_, 0);
lean_inc(v_ref_2822_);
v_msg_2823_ = lean_ctor_get(v_ex_2821_, 1);
lean_inc_ref(v_msg_2823_);
lean_dec_ref_known(v_ex_2821_, 2);
v___x_2824_ = l_Lean_logErrorAt___redArg(v_inst_2816_, v_inst_2817_, v_inst_2818_, v_inst_2819_, v_ref_2822_, v_msg_2823_);
return v___x_2824_;
}
else
{
lean_object* v_id_2825_; lean_object* v___f_2826_; uint8_t v___y_2828_; uint8_t v___x_2837_; 
v_id_2825_ = lean_ctor_get(v_ex_2821_, 0);
lean_inc(v_id_2825_);
lean_inc_ref(v_inst_2816_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2826_, 0, v_inst_2816_);
lean_closure_set(v___f_2826_, 1, v_inst_2817_);
lean_closure_set(v___f_2826_, 2, v_inst_2818_);
lean_closure_set(v___f_2826_, 3, v_inst_2819_);
v___x_2837_ = l_Lean_Elab_isAbortExceptionId(v_id_2825_);
if (v___x_2837_ == 0)
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Exception_isInterrupt(v_ex_2821_);
lean_dec_ref_known(v_ex_2821_, 2);
v___y_2828_ = v___x_2838_;
goto v___jp_2827_;
}
else
{
lean_dec_ref_known(v_ex_2821_, 2);
v___y_2828_ = v___x_2837_;
goto v___jp_2827_;
}
v___jp_2827_:
{
if (v___y_2828_ == 0)
{
lean_object* v_toBind_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_toBind_2829_ = lean_ctor_get(v_inst_2816_, 1);
lean_inc(v_toBind_2829_);
lean_dec_ref(v_inst_2816_);
v___x_2830_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2830_, 0, v_id_2825_);
v___x_2831_ = lean_apply_2(v_inst_2820_, lean_box(0), v___x_2830_);
v___x_2832_ = lean_apply_4(v_toBind_2829_, lean_box(0), lean_box(0), v___x_2831_, v___f_2826_);
return v___x_2832_;
}
else
{
lean_object* v_toApplicative_2833_; lean_object* v_toPure_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec_ref(v___f_2826_);
lean_dec(v_id_2825_);
lean_dec(v_inst_2820_);
v_toApplicative_2833_ = lean_ctor_get(v_inst_2816_, 0);
lean_inc_ref(v_toApplicative_2833_);
lean_dec_ref(v_inst_2816_);
v_toPure_2834_ = lean_ctor_get(v_toApplicative_2833_, 1);
lean_inc(v_toPure_2834_);
lean_dec_ref(v_toApplicative_2833_);
v___x_2835_ = lean_box(0);
v___x_2836_ = lean_apply_2(v_toPure_2834_, lean_box(0), v___x_2835_);
return v___x_2836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_inst_2844_, lean_object* v_ex_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Elab_logException___redArg(v_inst_2840_, v_inst_2841_, v_inst_2842_, v_inst_2843_, v_inst_2844_, v_ex_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_ex_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_Elab_logException___redArg(v_inst_2847_, v_inst_2848_, v_inst_2849_, v_inst_2850_, v_inst_2851_, v_ex_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v_tryCatch_2861_; lean_object* v___f_2862_; lean_object* v___x_2863_; 
v_tryCatch_2861_ = lean_ctor_get(v_inst_2856_, 1);
lean_inc(v_tryCatch_2861_);
lean_dec_ref(v_inst_2856_);
v___f_2862_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2862_, 0, v_inst_2854_);
lean_closure_set(v___f_2862_, 1, v_inst_2855_);
lean_closure_set(v___f_2862_, 2, v_inst_2857_);
lean_closure_set(v___f_2862_, 3, v_inst_2858_);
lean_closure_set(v___f_2862_, 4, v_inst_2859_);
v___x_2863_ = lean_apply_3(v_tryCatch_2861_, lean_box(0), v_x_2860_, v___f_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_x_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Elab_withLogging___redArg(v_inst_2865_, v_inst_2866_, v_inst_2867_, v_inst_2868_, v_inst_2869_, v_inst_2870_, v_x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2875_ = l_Lean_stringToMessageData(v___x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2876_, lean_object* v_ex_2877_, lean_object* v_toPure_2878_, lean_object* v_____do__lift_2879_){
_start:
{
lean_object* v_exPosition_2880_; lean_object* v_line_2881_; lean_object* v_column_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2902_; 
v_exPosition_2880_ = l_Lean_FileMap_toPosition(v_____do__lift_2879_, v_val_2876_);
v_line_2881_ = lean_ctor_get(v_exPosition_2880_, 0);
v_column_2882_ = lean_ctor_get(v_exPosition_2880_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_exPosition_2880_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2884_ = v_exPosition_2880_;
v_isShared_2885_ = v_isSharedCheck_2902_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_column_2882_);
lean_inc(v_line_2881_);
lean_dec(v_exPosition_2880_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2902_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2886_ = l_Nat_reprFast(v_line_2881_);
v___x_2887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
v___x_2888_ = l_Lean_MessageData_ofFormat(v___x_2887_);
v___x_2889_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2885_ == 0)
{
lean_ctor_set_tag(v___x_2884_, 7);
lean_ctor_set(v___x_2884_, 1, v___x_2889_);
lean_ctor_set(v___x_2884_, 0, v___x_2888_);
v___x_2891_ = v___x_2884_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2892_ = l_Nat_reprFast(v_column_2882_);
v___x_2893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofFormat(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2891_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = l_Lean_Exception_toMessageData(v_ex_2877_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_2899_);
return v___x_2900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2903_, lean_object* v_ex_2904_, lean_object* v_toPure_2905_, lean_object* v_____do__lift_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2903_, v_ex_2904_, v_toPure_2905_, v_____do__lift_2906_);
lean_dec(v_val_2903_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2908_, lean_object* v_toPure_2909_, lean_object* v_inst_2910_, lean_object* v_toBind_2911_, lean_object* v_pos_2912_){
_start:
{
lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = l_Lean_Exception_getRef(v_ex_2908_);
v___x_2914_ = 0;
v___x_2915_ = l_Lean_Syntax_getPos_x3f(v___x_2913_, v___x_2914_);
lean_dec(v___x_2913_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v_toBind_2911_);
lean_dec_ref(v_inst_2910_);
v___x_2916_ = l_Lean_Exception_toMessageData(v_ex_2908_);
v___x_2917_ = lean_apply_2(v_toPure_2909_, lean_box(0), v___x_2916_);
return v___x_2917_;
}
else
{
lean_object* v_val_2918_; uint8_t v___x_2919_; 
v_val_2918_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2919_ = lean_nat_dec_eq(v_pos_2912_, v_val_2918_);
if (v___x_2919_ == 0)
{
lean_object* v_toMonadFileMap_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; 
v_toMonadFileMap_2920_ = lean_ctor_get(v_inst_2910_, 0);
lean_inc(v_toMonadFileMap_2920_);
lean_dec_ref(v_inst_2910_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2921_, 0, v_val_2918_);
lean_closure_set(v___f_2921_, 1, v_ex_2908_);
lean_closure_set(v___f_2921_, 2, v_toPure_2909_);
v___x_2922_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v_toMonadFileMap_2920_, v___f_2921_);
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec(v_val_2918_);
lean_dec(v_toBind_2911_);
lean_dec_ref(v_inst_2910_);
v___x_2923_ = l_Lean_Exception_toMessageData(v_ex_2908_);
v___x_2924_ = lean_apply_2(v_toPure_2909_, lean_box(0), v___x_2923_);
return v___x_2924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2925_, lean_object* v_toPure_2926_, lean_object* v_inst_2927_, lean_object* v_toBind_2928_, lean_object* v_pos_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2925_, v_toPure_2926_, v_inst_2927_, v_toBind_2928_, v_pos_2929_);
lean_dec(v_pos_2929_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2931_, lean_object* v_inst_2932_, lean_object* v_ex_2933_){
_start:
{
lean_object* v_toApplicative_2934_; lean_object* v_toBind_2935_; lean_object* v_toPure_2936_; lean_object* v___x_2937_; lean_object* v___f_2938_; lean_object* v___x_2939_; 
v_toApplicative_2934_ = lean_ctor_get(v_inst_2931_, 0);
v_toBind_2935_ = lean_ctor_get(v_inst_2931_, 1);
lean_inc_n(v_toBind_2935_, 2);
v_toPure_2936_ = lean_ctor_get(v_toApplicative_2934_, 1);
lean_inc(v_toPure_2936_);
lean_inc_ref(v_inst_2932_);
v___x_2937_ = l_Lean_getRefPos___redArg(v_inst_2931_, v_inst_2932_);
v___f_2938_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2938_, 0, v_ex_2933_);
lean_closure_set(v___f_2938_, 1, v_toPure_2936_);
lean_closure_set(v___f_2938_, 2, v_inst_2932_);
lean_closure_set(v___f_2938_, 3, v_toBind_2935_);
v___x_2939_ = lean_apply_4(v_toBind_2935_, lean_box(0), lean_box(0), v___x_2937_, v___f_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_ex_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2941_, v_inst_2942_, v_ex_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2945_, v_inst_2946_, v_x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2951_ = l_Lean_stringToMessageData(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_____do__lift_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2956_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_msg_2952_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_toMessageList(v_____do__lift_2955_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_throwError___redArg(v_inst_2953_, v_inst_2954_, v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_msg_2964_, lean_object* v_exs_2965_){
_start:
{
lean_object* v_toBind_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; size_t v_sz_2969_; size_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_toBind_2966_ = lean_ctor_get(v_inst_2962_, 1);
lean_inc(v_toBind_2966_);
lean_inc_ref_n(v_inst_2962_, 2);
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2967_, 0, v_inst_2962_);
lean_closure_set(v___f_2967_, 1, v_inst_2963_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2968_, 0, v_msg_2964_);
lean_closure_set(v___f_2968_, 1, v_inst_2962_);
lean_closure_set(v___f_2968_, 2, v_inst_2961_);
v_sz_2969_ = lean_array_size(v_exs_2965_);
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2962_, v___f_2967_, v_sz_2969_, v___x_2970_, v_exs_2965_);
v___x_2972_ = lean_apply_4(v_toBind_2966_, lean_box(0), lean_box(0), v___x_2971_, v___f_2968_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2973_, lean_object* v_00_u03b1_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_msg_2978_, lean_object* v_exs_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2975_, v_inst_2976_, v_inst_2977_, v_msg_2978_, v_exs_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3048_ = 0;
v___x_3049_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3050_ = l_Lean_registerTraceClass(v___x_3047_, v___x_3048_, v___x_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec_ref_known(v___x_3050_, 1);
v___x_3051_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3052_ = l_Lean_registerTraceClass(v___x_3051_, v___x_3048_, v___x_3049_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref_known(v___x_3052_, 1);
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3054_ = 1;
v___x_3055_ = l_Lean_registerTraceClass(v___x_3053_, v___x_3054_, v___x_3049_);
return v___x_3055_;
}
else
{
return v___x_3052_;
}
}
else
{
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3057_;
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
