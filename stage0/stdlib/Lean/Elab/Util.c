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
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(139) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(91) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(150) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
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
lean_object* v_head_104_; lean_object* v_tail_105_; lean_object* v_before_106_; uint8_t v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_head_104_ = lean_ctor_get(v_x_102_, 0);
v_tail_105_ = lean_ctor_get(v_x_102_, 1);
v_before_106_ = lean_ctor_get(v_head_104_, 0);
v___x_107_ = 0;
v___x_108_ = l_Lean_Syntax_getPos_x3f(v_before_106_, v___x_107_);
v___x_109_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v___x_108_, v___x_101_);
lean_dec(v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_inc(v_head_104_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_head_104_);
return v___x_110_;
}
else
{
v_x_102_ = v_tail_105_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(lean_object* v___x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v___x_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef(lean_object* v_ref_115_, lean_object* v_macroStack_116_){
_start:
{
uint8_t v___x_117_; lean_object* v___x_118_; 
v___x_117_ = 0;
v___x_118_ = l_Lean_Syntax_getPos_x3f(v_ref_115_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v___x_119_; 
v___x_119_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_118_, v_macroStack_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_inc(v_ref_115_);
return v_ref_115_;
}
else
{
lean_object* v_val_120_; lean_object* v_before_121_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v___x_119_);
v_before_121_ = lean_ctor_get(v_val_120_, 0);
lean_inc(v_before_121_);
lean_dec(v_val_120_);
return v_before_121_;
}
}
else
{
lean_dec_ref(v___x_118_);
lean_inc(v_ref_115_);
return v_ref_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___boxed(lean_object* v_ref_122_, lean_object* v_macroStack_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Elab_getBetterRef(v_ref_122_, v_macroStack_123_);
lean_dec(v_macroStack_123_);
lean_dec(v_ref_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(lean_object* v_name_125_, lean_object* v_decl_126_, lean_object* v_ref_127_){
_start:
{
lean_object* v_defValue_129_; lean_object* v_descr_130_; lean_object* v_deprecation_x3f_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_defValue_129_ = lean_ctor_get(v_decl_126_, 0);
v_descr_130_ = lean_ctor_get(v_decl_126_, 1);
v_deprecation_x3f_131_ = lean_ctor_get(v_decl_126_, 2);
v___x_132_ = lean_alloc_ctor(1, 0, 1);
v___x_133_ = lean_unbox(v_defValue_129_);
lean_ctor_set_uint8(v___x_132_, 0, v___x_133_);
lean_inc(v_deprecation_x3f_131_);
lean_inc_ref(v_descr_130_);
lean_inc_n(v_name_125_, 2);
v___x_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_134_, 0, v_name_125_);
lean_ctor_set(v___x_134_, 1, v_ref_127_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
lean_ctor_set(v___x_134_, 3, v_descr_130_);
lean_ctor_set(v___x_134_, 4, v_deprecation_x3f_131_);
v___x_135_ = lean_register_option(v_name_125_, v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_144_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_defValue_129_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_name_125_);
lean_ctor_set(v___x_139_, 1, v_defValue_129_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_name_125_);
v_a_145_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_135_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_153_, lean_object* v_decl_154_, lean_object* v_ref_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_153_, v_decl_154_, v_ref_155_);
lean_dec_ref(v_decl_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_));
v___x_179_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_176_, v___x_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
return v_res_181_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1));
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__0(lean_object* v___x_187_, lean_object* v_msgData_188_, lean_object* v_elem_189_){
_start:
{
lean_object* v_before_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_202_; 
v_before_190_ = lean_ctor_get(v_elem_189_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_elem_189_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_elem_189_, 1);
lean_dec(v_unused_203_);
v___x_192_ = v_elem_189_;
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_before_190_);
lean_dec(v_elem_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 7);
lean_ctor_set(v___x_192_, 1, v___x_187_);
lean_ctor_set(v___x_192_, 0, v_msgData_188_);
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_msgData_188_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_187_);
v___x_195_ = v_reuseFailAlloc_201_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2, &l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2);
v___x_197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_MessageData_ofSyntax(v_before_190_);
v___x_199_ = l_Lean_indentD(v___x_198_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_197_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_box(1);
v___x_205_ = l_Lean_MessageData_ofFormat(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___f_207_; 
v___x_206_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__0), 3, 1);
lean_closure_set(v___f_207_, 0, v___x_206_);
return v___f_207_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3));
v___x_212_ = l_Lean_MessageData_ofFormat(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_213_, lean_object* v_toApplicative_214_, lean_object* v_msgData_215_, lean_object* v_macroStack_216_, lean_object* v_____do__lift_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_Elab_pp_macroStack;
v___x_219_ = l_Lean_Option_get___redArg(v___x_213_, v_____do__lift_217_, v___x_218_);
v___x_220_ = lean_unbox(v___x_219_);
lean_dec(v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v_toPure_221_; lean_object* v___x_222_; 
lean_dec(v_macroStack_216_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_214_);
v___x_222_ = lean_apply_2(v_toPure_221_, lean_box(0), v_msgData_215_);
return v___x_222_;
}
else
{
if (lean_obj_tag(v_macroStack_216_) == 0)
{
lean_object* v_toPure_223_; lean_object* v___x_224_; 
v_toPure_223_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_223_);
lean_dec_ref(v_toApplicative_214_);
v___x_224_ = lean_apply_2(v_toPure_223_, lean_box(0), v_msgData_215_);
return v___x_224_;
}
else
{
lean_object* v_head_225_; lean_object* v_after_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_243_; 
v_head_225_ = lean_ctor_get(v_macroStack_216_, 0);
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
v_toPure_230_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_230_);
lean_dec_ref(v_toApplicative_214_);
v___x_231_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_232_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 7);
lean_ctor_set(v___x_228_, 1, v___x_231_);
lean_ctor_set(v___x_228_, 0, v_msgData_215_);
v___x_234_ = v___x_228_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_msgData_215_);
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
v___x_240_ = l_List_foldl___redArg(v___f_232_, v_msgData_239_, v_macroStack_216_);
v___x_241_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_240_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_245_, lean_object* v_toApplicative_246_, lean_object* v_msgData_247_, lean_object* v_macroStack_248_, lean_object* v_____do__lift_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_245_, v_toApplicative_246_, v_msgData_247_, v_macroStack_248_, v_____do__lift_249_);
lean_dec_ref(v_____do__lift_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_msgData_253_, lean_object* v_macroStack_254_){
_start:
{
lean_object* v___x_255_; lean_object* v_toApplicative_256_; lean_object* v_toBind_257_; lean_object* v___f_258_; lean_object* v___x_259_; 
v___x_255_ = l_Lean_KVMap_instValueBool;
v_toApplicative_256_ = lean_ctor_get(v_inst_251_, 0);
lean_inc_ref(v_toApplicative_256_);
v_toBind_257_ = lean_ctor_get(v_inst_251_, 1);
lean_inc(v_toBind_257_);
lean_dec_ref(v_inst_251_);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_258_, 0, v___x_255_);
lean_closure_set(v___f_258_, 1, v_toApplicative_256_);
lean_closure_set(v___f_258_, 2, v_msgData_253_);
lean_closure_set(v___f_258_, 3, v_macroStack_254_);
v___x_259_ = lean_apply_4(v_toBind_257_, lean_box(0), lean_box(0), v_inst_252_, v___f_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_msgData_263_, lean_object* v_macroStack_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Elab_addMacroStack___redArg(v_inst_261_, v_inst_262_, v_msgData_263_, v_macroStack_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_268_ = l_Lean_stringToMessageData(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_____r_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_273_ = l_Lean_throwError___redArg(v_inst_269_, v_inst_270_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_274_, lean_object* v___f_275_, lean_object* v_toApplicative_276_, lean_object* v_____do__lift_277_){
_start:
{
uint8_t v___x_278_; 
lean_inc(v_k_274_);
v___x_278_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_277_, v_k_274_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v_toApplicative_276_);
lean_dec(v_k_274_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_apply_1(v___f_275_, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v_toPure_281_; lean_object* v___x_282_; 
lean_dec(v___f_275_);
v_toPure_281_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_281_);
lean_dec_ref(v_toApplicative_276_);
v___x_282_ = lean_apply_2(v_toPure_281_, lean_box(0), v_k_274_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_283_, lean_object* v___f_284_, lean_object* v_toApplicative_285_, lean_object* v_toBind_286_, lean_object* v_getEnv_287_, lean_object* v_____do__lift_288_){
_start:
{
lean_object* v_k_289_; lean_object* v___f_290_; lean_object* v___x_291_; 
v_k_289_ = l_Lean_mkPrivateName(v_____do__lift_288_, v_k_283_);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_290_, 0, v_k_289_);
lean_closure_set(v___f_290_, 1, v___f_284_);
lean_closure_set(v___f_290_, 2, v_toApplicative_285_);
v___x_291_ = lean_apply_4(v_toBind_286_, lean_box(0), lean_box(0), v_getEnv_287_, v___f_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_292_, lean_object* v___f_293_, lean_object* v_toApplicative_294_, lean_object* v_toBind_295_, lean_object* v_getEnv_296_, lean_object* v_____do__lift_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_292_, v___f_293_, v_toApplicative_294_, v_toBind_295_, v_getEnv_296_, v_____do__lift_297_);
lean_dec_ref(v_____do__lift_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_299_, lean_object* v_k_300_, lean_object* v_toBind_301_, lean_object* v_getEnv_302_, lean_object* v___f_303_, uint8_t v___x_304_, lean_object* v_____do__lift_305_){
_start:
{
uint8_t v_isExporting_313_; 
v_isExporting_313_ = lean_ctor_get_uint8(v_____do__lift_305_, sizeof(void*)*8);
if (v_isExporting_313_ == 0)
{
goto v___jp_309_;
}
else
{
if (v___x_304_ == 0)
{
lean_dec(v___f_303_);
lean_dec(v_getEnv_302_);
lean_dec(v_toBind_301_);
goto v___jp_306_;
}
else
{
goto v___jp_309_;
}
}
v___jp_306_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v___f_299_, v___x_307_);
return v___x_308_;
}
v___jp_309_:
{
uint8_t v___x_310_; 
v___x_310_ = l_Lean_isPrivateName(v_k_300_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v___f_299_);
v___x_311_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v_getEnv_302_, v___f_303_);
return v___x_311_;
}
else
{
if (v___x_304_ == 0)
{
lean_dec(v___f_303_);
lean_dec(v_getEnv_302_);
lean_dec(v_toBind_301_);
goto v___jp_306_;
}
else
{
lean_object* v___x_312_; 
lean_dec(v___f_299_);
v___x_312_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v_getEnv_302_, v___f_303_);
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_314_, lean_object* v_k_315_, lean_object* v_toBind_316_, lean_object* v_getEnv_317_, lean_object* v___f_318_, lean_object* v___x_319_, lean_object* v_____do__lift_320_){
_start:
{
uint8_t v___x_388__boxed_321_; lean_object* v_res_322_; 
v___x_388__boxed_321_ = lean_unbox(v___x_319_);
v_res_322_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_314_, v_k_315_, v_toBind_316_, v_getEnv_317_, v___f_318_, v___x_388__boxed_321_, v_____do__lift_320_);
lean_dec_ref(v_____do__lift_320_);
lean_dec(v_k_315_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_323_, lean_object* v___f_324_, lean_object* v_toBind_325_, lean_object* v_getEnv_326_, lean_object* v___f_327_, lean_object* v_toApplicative_328_, lean_object* v_____do__lift_329_){
_start:
{
uint8_t v___x_330_; 
lean_inc(v_k_323_);
v___x_330_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_329_, v_k_323_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
lean_dec_ref(v_toApplicative_328_);
v___x_331_ = lean_box(v___x_330_);
lean_inc(v_getEnv_326_);
lean_inc(v_toBind_325_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_332_, 0, v___f_324_);
lean_closure_set(v___f_332_, 1, v_k_323_);
lean_closure_set(v___f_332_, 2, v_toBind_325_);
lean_closure_set(v___f_332_, 3, v_getEnv_326_);
lean_closure_set(v___f_332_, 4, v___f_327_);
lean_closure_set(v___f_332_, 5, v___x_331_);
v___x_333_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v_getEnv_326_, v___f_332_);
return v___x_333_;
}
else
{
lean_object* v_toPure_334_; lean_object* v___x_335_; 
lean_dec(v___f_327_);
lean_dec(v_getEnv_326_);
lean_dec(v_toBind_325_);
lean_dec(v___f_324_);
v_toPure_334_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_inc(v_toPure_334_);
lean_dec_ref(v_toApplicative_328_);
v___x_335_ = lean_apply_2(v_toPure_334_, lean_box(0), v_k_323_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_k_339_){
_start:
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v_getEnv_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref_n(v_toApplicative_340_, 2);
v_toBind_341_ = lean_ctor_get(v_inst_336_, 1);
lean_inc_n(v_toBind_341_, 3);
v_getEnv_342_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_n(v_getEnv_342_, 3);
lean_dec_ref(v_inst_337_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_343_, 0, v_inst_336_);
lean_closure_set(v___f_343_, 1, v_inst_338_);
lean_inc_ref(v___f_343_);
lean_inc(v_k_339_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_344_, 0, v_k_339_);
lean_closure_set(v___f_344_, 1, v___f_343_);
lean_closure_set(v___f_344_, 2, v_toApplicative_340_);
lean_closure_set(v___f_344_, 3, v_toBind_341_);
lean_closure_set(v___f_344_, 4, v_getEnv_342_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_345_, 0, v_k_339_);
lean_closure_set(v___f_345_, 1, v___f_343_);
lean_closure_set(v___f_345_, 2, v_toBind_341_);
lean_closure_set(v___f_345_, 3, v_getEnv_342_);
lean_closure_set(v___f_345_, 4, v___f_344_);
lean_closure_set(v___f_345_, 5, v_toApplicative_340_);
v___x_346_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v_getEnv_342_, v___f_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_k_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_348_, v_inst_349_, v_inst_350_, v_k_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_k_356_, lean_object* v_pre_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_353_, v_inst_354_, v_inst_355_, v_k_356_, v_pre_357_, v_x_358_);
lean_dec_ref(v_x_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_k_363_, lean_object* v_x_364_){
_start:
{
switch(lean_obj_tag(v_x_364_))
{
case 1:
{
lean_object* v_toMonadExceptOf_365_; lean_object* v_pre_366_; lean_object* v_tryCatch_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_toMonadExceptOf_365_ = lean_ctor_get(v_inst_362_, 0);
v_pre_366_ = lean_ctor_get(v_x_364_, 0);
v_tryCatch_367_ = lean_ctor_get(v_toMonadExceptOf_365_, 1);
lean_inc(v_tryCatch_367_);
lean_inc(v_pre_366_);
lean_inc(v_k_363_);
lean_inc_ref(v_inst_362_);
lean_inc_ref(v_inst_361_);
lean_inc_ref(v_inst_360_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_368_, 0, v_inst_360_);
lean_closure_set(v___f_368_, 1, v_inst_361_);
lean_closure_set(v___f_368_, 2, v_inst_362_);
lean_closure_set(v___f_368_, 3, v_k_363_);
lean_closure_set(v___f_368_, 4, v_pre_366_);
v___x_369_ = l_Lean_Name_append(v_x_364_, v_k_363_);
v___x_370_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_360_, v_inst_361_, v_inst_362_, v___x_369_);
v___x_371_ = lean_apply_3(v_tryCatch_367_, lean_box(0), v___x_370_, v___f_368_);
return v___x_371_;
}
case 0:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_360_, v_inst_361_, v_inst_362_, v_k_363_);
return v___x_372_;
}
default: 
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_x_364_);
lean_dec(v_k_363_);
lean_dec_ref(v_inst_361_);
v___x_373_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_374_ = l_Lean_throwError___redArg(v_inst_360_, v_inst_362_, v___x_373_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_k_378_, lean_object* v_pre_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_375_, v_inst_376_, v_inst_377_, v_k_378_, v_pre_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_k_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_383_, v_inst_384_, v_inst_385_, v_k_386_, v_x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_389_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_ctor_set(v___x_394_, 3, v___x_393_);
lean_ctor_set(v___x_394_, 4, v___x_392_);
lean_ctor_set(v___x_394_, 5, v___x_392_);
lean_ctor_set(v___x_394_, 6, v___x_392_);
lean_ctor_set(v___x_394_, 7, v___x_392_);
lean_ctor_set(v___x_394_, 8, v___x_392_);
lean_ctor_set(v___x_394_, 9, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(32u);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_399_);
lean_ctor_set(v___x_403_, 3, v___x_399_);
lean_ctor_set_usize(v___x_403_, 4, v___x_398_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_box(1);
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_404_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_env_413_; lean_object* v_options_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_412_ = lean_st_ref_get(v___y_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_env_413_);
lean_dec(v___x_412_);
v_options_414_ = lean_ctor_get(v___y_409_, 2);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_414_);
v___x_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_417_, 0, v_env_413_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
lean_ctor_set(v___x_417_, 3, v_options_414_);
v___x_418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_msgData_408_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_ref_429_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_ref_429_ = lean_ctor_get(v___y_426_, 5);
v___x_430_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_425_, v___y_426_, v___y_427_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc(v_ref_429_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_ref_429_);
lean_ctor_set(v___x_435_, 1, v_a_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 1);
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___x_454_; lean_object* v_env_455_; uint8_t v___x_456_; 
v___x_454_ = lean_st_ref_get(v___y_447_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
lean_inc(v_k_445_);
v___x_456_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_455_, v_k_445_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v_env_474_; uint8_t v_isExporting_475_; 
v___x_457_ = lean_st_ref_get(v___y_447_);
v_env_474_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_457_);
v_isExporting_475_ = lean_ctor_get_uint8(v_env_474_, sizeof(void*)*8);
lean_dec_ref(v_env_474_);
if (v_isExporting_475_ == 0)
{
goto v___jp_458_;
}
else
{
if (v___x_456_ == 0)
{
lean_dec(v_k_445_);
v___y_450_ = v___y_446_;
v___y_451_ = v___y_447_;
goto v___jp_449_;
}
else
{
goto v___jp_458_;
}
}
v___jp_458_:
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_isPrivateName(v_k_445_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v_env_461_; lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_k_464_; uint8_t v___x_465_; 
v___x_460_ = lean_st_ref_get(v___y_447_);
v_env_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_env_461_);
lean_dec(v___x_460_);
v___x_462_ = lean_st_ref_get(v___y_447_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_463_);
lean_dec(v___x_462_);
v_k_464_ = l_Lean_mkPrivateName(v_env_461_, v_k_445_);
lean_dec_ref(v_env_461_);
lean_inc(v_k_464_);
v___x_465_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_463_, v_k_464_);
if (v___x_465_ == 0)
{
lean_dec(v_k_464_);
v___y_450_ = v___y_446_;
v___y_451_ = v___y_447_;
goto v___jp_449_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_k_464_);
return v___x_466_;
}
}
else
{
if (v___x_456_ == 0)
{
lean_dec(v_k_445_);
v___y_450_ = v___y_446_;
v___y_451_ = v___y_447_;
goto v___jp_449_;
}
else
{
lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v___x_469_; lean_object* v_env_470_; lean_object* v_k_471_; uint8_t v___x_472_; 
v___x_467_ = lean_st_ref_get(v___y_447_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = lean_st_ref_get(v___y_447_);
v_env_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_469_);
v_k_471_ = l_Lean_mkPrivateName(v_env_468_, v_k_445_);
lean_dec_ref(v_env_468_);
lean_inc(v_k_471_);
v___x_472_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_470_, v_k_471_);
if (v___x_472_ == 0)
{
lean_dec(v_k_471_);
v___y_450_ = v___y_446_;
v___y_451_ = v___y_447_;
goto v___jp_449_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_k_471_);
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v___x_476_; 
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_k_445_);
return v___x_476_;
}
v___jp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_453_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_452_, v___y_450_, v___y_451_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
switch(lean_obj_tag(v_x_483_))
{
case 1:
{
lean_object* v_pre_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_pre_487_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_pre_487_);
lean_inc(v_k_482_);
v___x_488_ = l_Lean_Name_append(v_x_483_, v_k_482_);
v___x_489_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_488_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec(v_pre_487_);
lean_dec(v_k_482_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; uint8_t v___y_492_; uint8_t v___x_494_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
v___x_494_ = l_Lean_Exception_isInterrupt(v_a_490_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Exception_isRuntime(v_a_490_);
v___y_492_ = v___x_495_;
goto v___jp_491_;
}
else
{
lean_dec(v_a_490_);
v___y_492_ = v___x_494_;
goto v___jp_491_;
}
v___jp_491_:
{
if (v___y_492_ == 0)
{
lean_dec_ref(v___x_489_);
v_x_483_ = v_pre_487_;
goto _start;
}
else
{
lean_dec(v_pre_487_);
lean_dec(v_k_482_);
return v___x_489_;
}
}
}
}
case 0:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_482_, v___y_484_, v___y_485_);
return v___x_496_;
}
default: 
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_x_483_);
lean_dec(v_k_482_);
v___x_497_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_498_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_497_, v___y_484_, v___y_485_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_499_, lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_499_, v_x_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_currNamespace_509_; lean_object* v___x_510_; 
v_currNamespace_509_ = lean_ctor_get(v_a_506_, 6);
lean_inc(v_currNamespace_509_);
v___x_510_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_505_, v_currNamespace_509_, v_a_506_, v_a_507_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_516_, lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_517_, v___y_518_, v___y_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_522_, lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_522_, v_msg_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_534_, lean_object* v_stx_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Attribute_Builtin_getId(v_stx_535_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___y_542_; uint8_t v___y_543_; lean_object* v___x_550_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_n(v_a_540_, 2);
lean_dec_ref(v___x_539_);
v___x_550_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_540_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_dec(v_a_540_);
lean_dec(v_defaultParserNamespace_534_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; uint8_t v___y_553_; uint8_t v___x_559_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
v___x_559_ = l_Lean_Exception_isInterrupt(v_a_551_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; 
v___x_560_ = l_Lean_Exception_isRuntime(v_a_551_);
v___y_553_ = v___x_560_;
goto v___jp_552_;
}
else
{
lean_dec(v_a_551_);
v___y_553_ = v___x_559_;
goto v___jp_552_;
}
v___jp_552_:
{
if (v___y_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v___x_550_);
lean_inc(v_a_540_);
v___x_554_ = l_Lean_Name_append(v_defaultParserNamespace_534_, v_a_540_);
v___x_555_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_554_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec(v_a_540_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; uint8_t v___x_557_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v___x_557_ = l_Lean_Exception_isInterrupt(v_a_556_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; 
v___x_558_ = l_Lean_Exception_isRuntime(v_a_556_);
v___y_542_ = v___x_555_;
v___y_543_ = v___x_558_;
goto v___jp_541_;
}
else
{
lean_dec(v_a_556_);
v___y_542_ = v___x_555_;
v___y_543_ = v___x_557_;
goto v___jp_541_;
}
}
}
else
{
lean_dec(v_a_540_);
lean_dec(v_defaultParserNamespace_534_);
return v___x_550_;
}
}
}
v___jp_541_:
{
if (v___y_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v___y_542_);
v___x_544_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_545_ = l_Lean_MessageData_ofName(v_a_540_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_548_, v_a_536_, v_a_537_);
return v___x_549_;
}
else
{
lean_dec(v_a_540_);
return v___y_542_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_534_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_561_, lean_object* v_stx_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_561_, v_stx_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_571_, lean_object* v_opts_572_, lean_object* v_constName_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_575_ = l_Lean_Environment_evalConstCheck___redArg(v_env_571_, v_opts_572_, v___x_574_, v_constName_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_576_, lean_object* v_opts_577_, lean_object* v_constName_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_576_, v_opts_577_, v_constName_578_);
lean_dec_ref(v_opts_577_);
return v_res_579_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_605_ = l_Lean_mkAtom(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_607_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_608_ = lean_array_push(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_618_ = l_Lean_mkAtom(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_620_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_621_ = lean_array_push(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_623_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_624_ = lean_box(2);
v___x_625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_627_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_628_ = lean_array_push(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_630_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_631_ = lean_box(2);
v___x_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_629_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_634_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_635_ = lean_array_push(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_637_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_638_ = lean_box(2);
v___x_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_636_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_641_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_642_ = lean_array_push(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_644_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_645_ = lean_box(2);
v___x_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_643_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_648_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_649_ = lean_array_push(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_651_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_652_ = lean_box(2);
v___x_653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_650_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_655_, lean_object* v_declName_656_, lean_object* v_kind_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
if (v_builtin_655_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_declName_656_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_656_, v___y_658_, v___y_659_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_664_, lean_object* v_declName_665_, lean_object* v_kind_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_builtin_boxed_670_; lean_object* v_res_671_; 
v_builtin_boxed_670_ = lean_unbox(v_builtin_664_);
v_res_671_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_670_, v_declName_665_, v_kind_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v_kind_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v_infoState_676_; uint8_t v_enabled_677_; 
v___x_675_ = lean_st_ref_get(v___y_673_);
v_infoState_676_ = lean_ctor_get(v___x_675_, 7);
lean_inc_ref(v_infoState_676_);
lean_dec(v___x_675_);
v_enabled_677_ = lean_ctor_get_uint8(v_infoState_676_, sizeof(void*)*3);
lean_dec_ref(v_infoState_676_);
if (v_enabled_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref(v_t_672_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v_infoState_681_; lean_object* v_env_682_; lean_object* v_nextMacroScope_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_traceState_686_; lean_object* v_cache_687_; lean_object* v_messages_688_; lean_object* v_snapshotTasks_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_711_; 
v___x_680_ = lean_st_ref_take(v___y_673_);
v_infoState_681_ = lean_ctor_get(v___x_680_, 7);
v_env_682_ = lean_ctor_get(v___x_680_, 0);
v_nextMacroScope_683_ = lean_ctor_get(v___x_680_, 1);
v_ngen_684_ = lean_ctor_get(v___x_680_, 2);
v_auxDeclNGen_685_ = lean_ctor_get(v___x_680_, 3);
v_traceState_686_ = lean_ctor_get(v___x_680_, 4);
v_cache_687_ = lean_ctor_get(v___x_680_, 5);
v_messages_688_ = lean_ctor_get(v___x_680_, 6);
v_snapshotTasks_689_ = lean_ctor_get(v___x_680_, 8);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_711_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_711_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snapshotTasks_689_);
lean_inc(v_infoState_681_);
lean_inc(v_messages_688_);
lean_inc(v_cache_687_);
lean_inc(v_traceState_686_);
lean_inc(v_auxDeclNGen_685_);
lean_inc(v_ngen_684_);
lean_inc(v_nextMacroScope_683_);
lean_inc(v_env_682_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_711_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v_enabled_693_; lean_object* v_assignment_694_; lean_object* v_lazyAssignment_695_; lean_object* v_trees_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_710_; 
v_enabled_693_ = lean_ctor_get_uint8(v_infoState_681_, sizeof(void*)*3);
v_assignment_694_ = lean_ctor_get(v_infoState_681_, 0);
v_lazyAssignment_695_ = lean_ctor_get(v_infoState_681_, 1);
v_trees_696_ = lean_ctor_get(v_infoState_681_, 2);
v_isSharedCheck_710_ = !lean_is_exclusive(v_infoState_681_);
if (v_isSharedCheck_710_ == 0)
{
v___x_698_ = v_infoState_681_;
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_trees_696_);
lean_inc(v_lazyAssignment_695_);
lean_inc(v_assignment_694_);
lean_dec(v_infoState_681_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_PersistentArray_push___redArg(v_trees_696_, v_t_672_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_assignment_694_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_lazyAssignment_695_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v___x_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_709_, sizeof(void*)*3, v_enabled_693_);
v___x_702_ = v_reuseFailAlloc_709_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 7, v___x_702_);
v___x_704_ = v___x_691_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_env_682_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_nextMacroScope_683_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_ngen_684_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_auxDeclNGen_685_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_traceState_686_);
lean_ctor_set(v_reuseFailAlloc_708_, 5, v_cache_687_);
lean_ctor_set(v_reuseFailAlloc_708_, 6, v_messages_688_);
lean_ctor_set(v_reuseFailAlloc_708_, 7, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 8, v_snapshotTasks_689_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_st_ref_set(v___y_673_, v___x_704_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_712_, v___y_713_);
lean_dec(v___y_713_);
return v_res_715_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(32u);
v___x_717_ = lean_mk_empty_array_with_capacity(v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_719_ = ((size_t)5ULL);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_unsigned_to_nat(32u);
v___x_722_ = lean_mk_empty_array_with_capacity(v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_724_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
lean_ctor_set(v___x_724_, 2, v___x_720_);
lean_ctor_set(v___x_724_, 3, v___x_720_);
lean_ctor_set_usize(v___x_724_, 4, v___x_719_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; lean_object* v_infoState_730_; uint8_t v_enabled_731_; 
v___x_729_ = lean_st_ref_get(v___y_727_);
v_infoState_730_ = lean_ctor_get(v___x_729_, 7);
lean_inc_ref(v_infoState_730_);
lean_dec(v___x_729_);
v_enabled_731_ = lean_ctor_get_uint8(v_infoState_730_, sizeof(void*)*3);
lean_dec_ref(v_infoState_730_);
if (v_enabled_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_t_725_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v_t_725_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_735_, v___y_727_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_741_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_763_, lean_object* v_declHint_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_env_768_; uint8_t v___x_769_; 
v___x_767_ = lean_st_ref_get(v___y_765_);
v_env_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_ref(v_env_768_);
lean_dec(v___x_767_);
v___x_769_ = l_Lean_Name_isAnonymous(v_declHint_764_);
if (v___x_769_ == 0)
{
uint8_t v_isExporting_770_; 
v_isExporting_770_ = lean_ctor_get_uint8(v_env_768_, sizeof(void*)*8);
if (v_isExporting_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_env_768_);
lean_dec(v_declHint_764_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_msg_763_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; uint8_t v___x_773_; 
lean_inc_ref(v_env_768_);
v___x_772_ = l_Lean_Environment_setExporting(v_env_768_, v___x_769_);
lean_inc(v_declHint_764_);
lean_inc_ref(v___x_772_);
v___x_773_ = l_Lean_Environment_contains(v___x_772_, v_declHint_764_, v_isExporting_770_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v___x_772_);
lean_dec_ref(v_env_768_);
lean_dec(v_declHint_764_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_msg_763_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_c_780_; lean_object* v___x_781_; 
v___x_775_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_776_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_777_ = l_Lean_Options_empty;
v___x_778_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_778_, 0, v___x_772_);
lean_ctor_set(v___x_778_, 1, v___x_775_);
lean_ctor_set(v___x_778_, 2, v___x_776_);
lean_ctor_set(v___x_778_, 3, v___x_777_);
lean_inc(v_declHint_764_);
v___x_779_ = l_Lean_MessageData_ofConstName(v_declHint_764_, v___x_769_);
v_c_780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_780_, 0, v___x_778_);
lean_ctor_set(v_c_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_768_, v_declHint_764_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_env_768_);
lean_dec(v_declHint_764_);
v___x_782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_c_780_);
v___x_784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_MessageData_note(v___x_785_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v_msg_763_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_824_; 
v_val_789_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_824_ == 0)
{
v___x_791_ = v___x_781_;
v_isShared_792_ = v_isSharedCheck_824_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_val_789_);
lean_dec(v___x_781_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_824_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_mod_796_; uint8_t v___x_797_; 
v___x_793_ = lean_box(0);
v___x_794_ = l_Lean_Environment_header(v_env_768_);
lean_dec_ref(v_env_768_);
v___x_795_ = l_Lean_EnvironmentHeader_moduleNames(v___x_794_);
v_mod_796_ = lean_array_get(v___x_793_, v___x_795_, v_val_789_);
lean_dec(v_val_789_);
lean_dec_ref(v___x_795_);
v___x_797_ = l_Lean_isPrivateName(v_declHint_764_);
lean_dec(v_declHint_764_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_798_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_c_780_);
v___x_800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_MessageData_ofName(v_mod_796_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = l_Lean_MessageData_note(v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v_msg_763_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 0);
lean_ctor_set(v___x_791_, 0, v___x_807_);
v___x_809_ = v___x_791_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_c_780_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_MessageData_ofName(v_mod_796_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_MessageData_note(v___x_818_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v_msg_763_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 0);
lean_ctor_set(v___x_791_, 0, v___x_820_);
v___x_822_ = v___x_791_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_825_; 
lean_dec_ref(v_env_768_);
lean_dec(v_declHint_764_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_msg_763_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_826_, lean_object* v_declHint_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_826_, v_declHint_827_, v___y_828_);
lean_dec(v___y_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_831_, lean_object* v_declHint_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_846_; 
v___x_836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_831_, v_declHint_832_, v___y_834_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_846_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = l_Lean_unknownIdentifierMessageTag;
v___x_842_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_a_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_847_, lean_object* v_declHint_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_847_, v_declHint_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_853_, lean_object* v_msg_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_fileName_858_; lean_object* v_fileMap_859_; lean_object* v_options_860_; lean_object* v_currRecDepth_861_; lean_object* v_maxRecDepth_862_; lean_object* v_ref_863_; lean_object* v_currNamespace_864_; lean_object* v_openDecls_865_; lean_object* v_initHeartbeats_866_; lean_object* v_maxHeartbeats_867_; lean_object* v_quotContext_868_; lean_object* v_currMacroScope_869_; uint8_t v_diag_870_; lean_object* v_cancelTk_x3f_871_; uint8_t v_suppressElabErrors_872_; lean_object* v_inheritedTraceOptions_873_; lean_object* v_ref_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_fileName_858_ = lean_ctor_get(v___y_855_, 0);
v_fileMap_859_ = lean_ctor_get(v___y_855_, 1);
v_options_860_ = lean_ctor_get(v___y_855_, 2);
v_currRecDepth_861_ = lean_ctor_get(v___y_855_, 3);
v_maxRecDepth_862_ = lean_ctor_get(v___y_855_, 4);
v_ref_863_ = lean_ctor_get(v___y_855_, 5);
v_currNamespace_864_ = lean_ctor_get(v___y_855_, 6);
v_openDecls_865_ = lean_ctor_get(v___y_855_, 7);
v_initHeartbeats_866_ = lean_ctor_get(v___y_855_, 8);
v_maxHeartbeats_867_ = lean_ctor_get(v___y_855_, 9);
v_quotContext_868_ = lean_ctor_get(v___y_855_, 10);
v_currMacroScope_869_ = lean_ctor_get(v___y_855_, 11);
v_diag_870_ = lean_ctor_get_uint8(v___y_855_, sizeof(void*)*14);
v_cancelTk_x3f_871_ = lean_ctor_get(v___y_855_, 12);
v_suppressElabErrors_872_ = lean_ctor_get_uint8(v___y_855_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_873_ = lean_ctor_get(v___y_855_, 13);
v_ref_874_ = l_Lean_replaceRef(v_ref_853_, v_ref_863_);
lean_inc_ref(v_inheritedTraceOptions_873_);
lean_inc(v_cancelTk_x3f_871_);
lean_inc(v_currMacroScope_869_);
lean_inc(v_quotContext_868_);
lean_inc(v_maxHeartbeats_867_);
lean_inc(v_initHeartbeats_866_);
lean_inc(v_openDecls_865_);
lean_inc(v_currNamespace_864_);
lean_inc(v_maxRecDepth_862_);
lean_inc(v_currRecDepth_861_);
lean_inc_ref(v_options_860_);
lean_inc_ref(v_fileMap_859_);
lean_inc_ref(v_fileName_858_);
v___x_875_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_875_, 0, v_fileName_858_);
lean_ctor_set(v___x_875_, 1, v_fileMap_859_);
lean_ctor_set(v___x_875_, 2, v_options_860_);
lean_ctor_set(v___x_875_, 3, v_currRecDepth_861_);
lean_ctor_set(v___x_875_, 4, v_maxRecDepth_862_);
lean_ctor_set(v___x_875_, 5, v_ref_874_);
lean_ctor_set(v___x_875_, 6, v_currNamespace_864_);
lean_ctor_set(v___x_875_, 7, v_openDecls_865_);
lean_ctor_set(v___x_875_, 8, v_initHeartbeats_866_);
lean_ctor_set(v___x_875_, 9, v_maxHeartbeats_867_);
lean_ctor_set(v___x_875_, 10, v_quotContext_868_);
lean_ctor_set(v___x_875_, 11, v_currMacroScope_869_);
lean_ctor_set(v___x_875_, 12, v_cancelTk_x3f_871_);
lean_ctor_set(v___x_875_, 13, v_inheritedTraceOptions_873_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*14, v_diag_870_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*14 + 1, v_suppressElabErrors_872_);
v___x_876_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_854_, v___x_875_, v___y_856_);
lean_dec_ref(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_877_, v_msg_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_ref_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_883_, lean_object* v_msg_884_, lean_object* v_declHint_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v_a_890_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_884_, v_declHint_885_, v___y_886_, v___y_887_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_883_, v_a_890_, v___y_886_, v___y_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_892_, lean_object* v_msg_893_, lean_object* v_declHint_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_892_, v_msg_893_, v_declHint_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v_ref_892_);
return v_res_898_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_902_, lean_object* v_constName_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_907_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_908_ = 0;
lean_inc(v_constName_903_);
v___x_909_ = l_Lean_MessageData_ofConstName(v_constName_903_, v___x_908_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_907_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_902_, v___x_912_, v_constName_903_, v___y_904_, v___y_905_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_914_, lean_object* v_constName_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_914_, v_constName_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v_ref_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_ref_924_; lean_object* v___x_925_; 
v_ref_924_ = lean_ctor_get(v___y_921_, 5);
v___x_925_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_924_, v_constName_920_, v___y_921_, v___y_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v_env_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_st_ref_get(v___y_933_);
v_env_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_env_936_);
lean_dec(v___x_935_);
v___x_937_ = 0;
lean_inc(v_constName_931_);
v___x_938_ = l_Lean_Environment_findConstVal_x3f(v_env_936_, v_constName_931_, v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_931_, v___y_932_, v___y_933_);
return v___x_939_;
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_constName_931_);
v_val_940_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_938_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v___x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 0);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
if (lean_obj_tag(v_a_953_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = l_List_reverse___redArg(v_a_954_);
return v___x_955_;
}
else
{
lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_966_; 
v_head_956_ = lean_ctor_get(v_a_953_, 0);
v_tail_957_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_966_ == 0)
{
v___x_959_ = v_a_953_;
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tail_957_);
lean_inc(v_head_956_);
lean_dec(v_a_953_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_966_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = l_Lean_mkLevelParam(v_head_956_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_a_954_);
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_954_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_a_953_ = v_tail_957_;
v_a_954_ = v___x_963_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc(v_constName_967_);
v___x_971_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_983_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_983_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_983_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_983_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_levelParams_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_levelParams_976_ = lean_ctor_get(v_a_972_, 1);
lean_inc(v_levelParams_976_);
lean_dec(v_a_972_);
v___x_977_ = lean_box(0);
v___x_978_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_976_, v___x_977_);
v___x_979_ = l_Lean_mkConst(v_constName_967_, v___x_978_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_979_);
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_constName_967_);
v_a_984_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_971_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_971_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_997_, lean_object* v_n_998_, lean_object* v_expectedType_x3f_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_998_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v_stx_997_);
v___x_1007_ = l_Lean_LocalContext_empty;
v___x_1008_ = 0;
v___x_1009_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
lean_ctor_set(v___x_1009_, 2, v_expectedType_x3f_999_);
lean_ctor_set(v___x_1009_, 3, v_a_1004_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*4, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*4 + 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
v___x_1011_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1010_, v___y_1000_, v___y_1001_);
return v___x_1011_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_expectedType_x3f_999_);
lean_dec(v_stx_997_);
v_a_1012_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1003_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1003_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1020_, lean_object* v_n_1021_, lean_object* v_expectedType_x3f_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1020_, v_n_1021_, v_expectedType_x3f_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1027_, lean_object* v_i_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = lean_array_get_size(v_keys_1027_);
v___x_1031_ = lean_nat_dec_lt(v_i_1028_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec(v_i_1028_);
return v___x_1031_;
}
else
{
lean_object* v_k_x27_1032_; uint8_t v___x_1033_; 
v_k_x27_1032_ = lean_array_fget_borrowed(v_keys_1027_, v_i_1028_);
v___x_1033_ = l_Lean_instBEqExtraModUse_beq(v_k_1029_, v_k_x27_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_nat_add(v_i_1028_, v___x_1034_);
lean_dec(v_i_1028_);
v_i_1028_ = v___x_1035_;
goto _start;
}
else
{
lean_dec(v_i_1028_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1037_, lean_object* v_i_1038_, lean_object* v_k_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1037_, v_i_1038_, v_k_1039_);
lean_dec_ref(v_k_1039_);
lean_dec_ref(v_keys_1037_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; 
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = ((size_t)1ULL);
v___x_1044_ = lean_usize_shift_left(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; 
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1047_ = lean_usize_sub(v___x_1046_, v___x_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1048_, size_t v_x_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1048_) == 0)
{
lean_object* v_es_1051_; lean_object* v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v_j_1056_; lean_object* v___x_1057_; 
v_es_1051_ = lean_ctor_get(v_x_1048_, 0);
v___x_1052_ = lean_box(2);
v___x_1053_ = ((size_t)5ULL);
v___x_1054_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1055_ = lean_usize_land(v_x_1049_, v___x_1054_);
v_j_1056_ = lean_usize_to_nat(v___x_1055_);
v___x_1057_ = lean_array_get_borrowed(v___x_1052_, v_es_1051_, v_j_1056_);
lean_dec(v_j_1056_);
switch(lean_obj_tag(v___x_1057_))
{
case 0:
{
lean_object* v_key_1058_; uint8_t v___x_1059_; 
v_key_1058_ = lean_ctor_get(v___x_1057_, 0);
v___x_1059_ = l_Lean_instBEqExtraModUse_beq(v_x_1050_, v_key_1058_);
return v___x_1059_;
}
case 1:
{
lean_object* v_node_1060_; size_t v___x_1061_; 
v_node_1060_ = lean_ctor_get(v___x_1057_, 0);
v___x_1061_ = lean_usize_shift_right(v_x_1049_, v___x_1053_);
v_x_1048_ = v_node_1060_;
v_x_1049_ = v___x_1061_;
goto _start;
}
default: 
{
uint8_t v___x_1063_; 
v___x_1063_ = 0;
return v___x_1063_;
}
}
}
else
{
lean_object* v_ks_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_ks_1064_ = lean_ctor_get(v_x_1048_, 0);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1064_, v___x_1065_, v_x_1050_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
size_t v_x_6766__boxed_1070_; uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_x_6766__boxed_1070_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_res_1071_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1067_, v_x_6766__boxed_1070_, v_x_1069_);
lean_dec_ref(v_x_1069_);
lean_dec_ref(v_x_1067_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
uint64_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = l_Lean_instHashableExtraModUse_hash(v_x_1074_);
v___x_1076_ = lean_uint64_to_usize(v___x_1075_);
v___x_1077_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1073_, v___x_1076_, v_x_1074_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1078_, v_x_1079_);
lean_dec_ref(v_x_1079_);
lean_dec_ref(v_x_1078_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1082_; double v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_float_of_nat(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1087_, lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_ref_1092_; lean_object* v___x_1093_; lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1138_; 
v_ref_1092_ = lean_ctor_get(v___y_1089_, 5);
v___x_1093_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1088_, v___y_1089_, v___y_1090_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1138_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1138_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v_traceState_1099_; lean_object* v_env_1100_; lean_object* v_nextMacroScope_1101_; lean_object* v_ngen_1102_; lean_object* v_auxDeclNGen_1103_; lean_object* v_cache_1104_; lean_object* v_messages_1105_; lean_object* v_infoState_1106_; lean_object* v_snapshotTasks_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1137_; 
v___x_1098_ = lean_st_ref_take(v___y_1090_);
v_traceState_1099_ = lean_ctor_get(v___x_1098_, 4);
v_env_1100_ = lean_ctor_get(v___x_1098_, 0);
v_nextMacroScope_1101_ = lean_ctor_get(v___x_1098_, 1);
v_ngen_1102_ = lean_ctor_get(v___x_1098_, 2);
v_auxDeclNGen_1103_ = lean_ctor_get(v___x_1098_, 3);
v_cache_1104_ = lean_ctor_get(v___x_1098_, 5);
v_messages_1105_ = lean_ctor_get(v___x_1098_, 6);
v_infoState_1106_ = lean_ctor_get(v___x_1098_, 7);
v_snapshotTasks_1107_ = lean_ctor_get(v___x_1098_, 8);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1109_ = v___x_1098_;
v_isShared_1110_ = v_isSharedCheck_1137_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snapshotTasks_1107_);
lean_inc(v_infoState_1106_);
lean_inc(v_messages_1105_);
lean_inc(v_cache_1104_);
lean_inc(v_traceState_1099_);
lean_inc(v_auxDeclNGen_1103_);
lean_inc(v_ngen_1102_);
lean_inc(v_nextMacroScope_1101_);
lean_inc(v_env_1100_);
lean_dec(v___x_1098_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1137_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint64_t v_tid_1111_; lean_object* v_traces_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1136_; 
v_tid_1111_ = lean_ctor_get_uint64(v_traceState_1099_, sizeof(void*)*1);
v_traces_1112_ = lean_ctor_get(v_traceState_1099_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_traceState_1099_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1114_ = v_traceState_1099_;
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_traces_1112_);
lean_dec(v_traceState_1099_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; double v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1118_ = 0;
v___x_1119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1120_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1120_, 0, v_cls_1087_);
lean_ctor_set(v___x_1120_, 1, v___x_1116_);
lean_ctor_set(v___x_1120_, 2, v___x_1119_);
lean_ctor_set_float(v___x_1120_, sizeof(void*)*3, v___x_1117_);
lean_ctor_set_float(v___x_1120_, sizeof(void*)*3 + 8, v___x_1117_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3 + 16, v___x_1118_);
v___x_1121_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1122_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v_a_1094_);
lean_ctor_set(v___x_1122_, 2, v___x_1121_);
lean_inc(v_ref_1092_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_ref_1092_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_PersistentArray_push___redArg(v_traces_1112_, v___x_1123_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1124_);
v___x_1126_ = v___x_1114_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1124_);
lean_ctor_set_uint64(v_reuseFailAlloc_1135_, sizeof(void*)*1, v_tid_1111_);
v___x_1126_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v___x_1126_);
v___x_1128_ = v___x_1109_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_env_1100_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_nextMacroScope_1101_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_ngen_1102_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_auxDeclNGen_1103_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_cache_1104_);
lean_ctor_set(v_reuseFailAlloc_1134_, 6, v_messages_1105_);
lean_ctor_set(v_reuseFailAlloc_1134_, 7, v_infoState_1106_);
lean_ctor_set(v_reuseFailAlloc_1134_, 8, v_snapshotTasks_1107_);
v___x_1128_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = lean_st_ref_set(v___y_1090_, v___x_1128_);
v___x_1130_ = lean_box(0);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1130_);
v___x_1132_ = v___x_1096_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1139_, lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1139_, v_msg_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1144_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1148_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1149_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1148_, v___x_1147_);
return v___x_1149_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_cls_1169_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1170_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1171_ = l_Lean_Name_append(v___x_1170_, v_cls_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1182_, uint8_t v_isMeta_1183_, lean_object* v_hint_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; uint8_t v_isExporting_1190_; lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v___x_1193_; lean_object* v_entry_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___y_1199_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_env_1189_);
lean_dec(v___x_1188_);
v_isExporting_1190_ = lean_ctor_get_uint8(v_env_1189_, sizeof(void*)*8);
lean_dec_ref(v_env_1189_);
v___x_1191_ = lean_st_ref_get(v___y_1186_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1182_);
v_entry_1194_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1194_, 0, v_mod_1182_);
lean_ctor_set_uint8(v_entry_1194_, sizeof(void*)*1, v_isExporting_1190_);
lean_ctor_set_uint8(v_entry_1194_, sizeof(void*)*1 + 1, v_isMeta_1183_);
v___x_1195_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1196_ = lean_box(1);
v___x_1197_ = lean_box(0);
v___x_1224_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1193_, v___x_1195_, v_env_1192_, v___x_1196_, v___x_1197_);
v___x_1225_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1224_, v_entry_1194_);
lean_dec(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v_options_1226_; uint8_t v_hasTrace_1227_; 
v_options_1226_ = lean_ctor_get(v___y_1185_, 2);
v_hasTrace_1227_ = lean_ctor_get_uint8(v_options_1226_, sizeof(void*)*1);
if (v_hasTrace_1227_ == 0)
{
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_object* v_inheritedTraceOptions_1228_; lean_object* v_cls_1229_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_inheritedTraceOptions_1228_ = lean_ctor_get(v___y_1185_, 13);
v_cls_1229_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1249_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
v___x_1250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1228_, v_options_1226_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1251_; lean_object* v___y_1253_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
if (v_isExporting_1190_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22));
v___y_1253_ = v___x_1260_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23));
v___y_1253_ = v___x_1261_;
goto v___jp_1252_;
}
v___jp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref(v___y_1253_);
v___x_1254_ = l_Lean_stringToMessageData(v___y_1253_);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1251_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
if (v_isMeta_1183_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1236_ = v___x_1257_;
v___y_1237_ = v___x_1258_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21));
v___y_1236_ = v___x_1257_;
v___y_1237_ = v___x_1259_;
goto v___jp_1235_;
}
}
}
v___jp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1231_);
lean_ctor_set(v___x_1233_, 1, v___y_1232_);
v___x_1234_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1229_, v___x_1233_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_dec_ref(v___x_1234_);
v___y_1199_ = v___y_1186_;
goto v___jp_1198_;
}
else
{
lean_dec_ref(v_entry_1194_);
return v___x_1234_;
}
}
v___jp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
lean_inc_ref(v___y_1237_);
v___x_1238_ = l_Lean_stringToMessageData(v___y_1237_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_MessageData_ofName(v_mod_1182_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_Name_isAnonymous(v_hint_1184_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1246_ = l_Lean_MessageData_ofName(v_hint_1184_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___y_1231_ = v___x_1243_;
v___y_1232_ = v___x_1247_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_hint_1184_);
v___x_1248_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1231_ = v___x_1243_;
v___y_1232_ = v___x_1248_;
goto v___jp_1230_;
}
}
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v_entry_1194_);
lean_dec(v_hint_1184_);
lean_dec(v_mod_1182_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v_toEnvExtension_1201_; lean_object* v_env_1202_; lean_object* v_nextMacroScope_1203_; lean_object* v_ngen_1204_; lean_object* v_auxDeclNGen_1205_; lean_object* v_traceState_1206_; lean_object* v_messages_1207_; lean_object* v_infoState_1208_; lean_object* v_snapshotTasks_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1222_; 
v___x_1200_ = lean_st_ref_take(v___y_1199_);
v_toEnvExtension_1201_ = lean_ctor_get(v___x_1195_, 0);
v_env_1202_ = lean_ctor_get(v___x_1200_, 0);
v_nextMacroScope_1203_ = lean_ctor_get(v___x_1200_, 1);
v_ngen_1204_ = lean_ctor_get(v___x_1200_, 2);
v_auxDeclNGen_1205_ = lean_ctor_get(v___x_1200_, 3);
v_traceState_1206_ = lean_ctor_get(v___x_1200_, 4);
v_messages_1207_ = lean_ctor_get(v___x_1200_, 6);
v_infoState_1208_ = lean_ctor_get(v___x_1200_, 7);
v_snapshotTasks_1209_ = lean_ctor_get(v___x_1200_, 8);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1200_, 5);
lean_dec(v_unused_1223_);
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1222_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_snapshotTasks_1209_);
lean_inc(v_infoState_1208_);
lean_inc(v_messages_1207_);
lean_inc(v_traceState_1206_);
lean_inc(v_auxDeclNGen_1205_);
lean_inc(v_ngen_1204_);
lean_inc(v_nextMacroScope_1203_);
lean_inc(v_env_1202_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1222_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_asyncMode_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v_asyncMode_1213_ = lean_ctor_get(v_toEnvExtension_1201_, 2);
v___x_1214_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1195_, v_env_1202_, v_entry_1194_, v_asyncMode_1213_, v___x_1197_);
v___x_1215_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 5, v___x_1215_);
lean_ctor_set(v___x_1211_, 0, v___x_1214_);
v___x_1217_ = v___x_1211_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_nextMacroScope_1203_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_ngen_1204_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_auxDeclNGen_1205_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_traceState_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 5, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1221_, 6, v_messages_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 7, v_infoState_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 8, v_snapshotTasks_1209_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_st_ref_set(v___y_1199_, v___x_1217_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1264_, lean_object* v_isMeta_1265_, lean_object* v_hint_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v_isMeta_boxed_1270_; lean_object* v_res_1271_; 
v_isMeta_boxed_1270_ = lean_unbox(v_isMeta_1265_);
v_res_1271_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1264_, v_isMeta_boxed_1270_, v_hint_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1272_, lean_object* v_declName_1273_, lean_object* v_as_1274_, size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_declName_1273_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1277_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v_modules_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v_toImport_1288_; lean_object* v_module_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1283_ = l_Lean_Environment_header(v___x_1272_);
v_modules_1284_ = lean_ctor_get(v___x_1283_, 3);
lean_inc_ref(v_modules_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1286_ = lean_array_uget_borrowed(v_as_1274_, v_i_1276_);
v___x_1287_ = lean_array_get(v___x_1285_, v_modules_1284_, v_a_1286_);
lean_dec_ref(v_modules_1284_);
v_toImport_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc_ref(v_toImport_1288_);
lean_dec(v___x_1287_);
v_module_1289_ = lean_ctor_get(v_toImport_1288_, 0);
lean_inc(v_module_1289_);
lean_dec_ref(v_toImport_1288_);
v___x_1290_ = 0;
lean_inc(v_declName_1273_);
v___x_1291_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1289_, v___x_1290_, v_declName_1273_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; 
lean_dec_ref(v___x_1291_);
v___x_1292_ = lean_box(0);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1276_, v___x_1293_);
v_i_1276_ = v___x_1294_;
v_b_1277_ = v___x_1292_;
goto _start;
}
else
{
lean_dec(v_declName_1273_);
return v___x_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1296_, lean_object* v_declName_1297_, lean_object* v_as_1298_, lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1296_, v_declName_1297_, v_as_1298_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v_as_1298_);
lean_dec_ref(v___x_1296_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
else
{
lean_object* v_key_1311_; lean_object* v_value_1312_; lean_object* v_tail_1313_; uint8_t v___x_1314_; 
v_key_1311_ = lean_ctor_get(v_x_1309_, 0);
v_value_1312_ = lean_ctor_get(v_x_1309_, 1);
v_tail_1313_ = lean_ctor_get(v_x_1309_, 2);
v___x_1314_ = lean_name_eq(v_key_1311_, v_a_1308_);
if (v___x_1314_ == 0)
{
v_x_1309_ = v_tail_1313_;
goto _start;
}
else
{
lean_object* v___x_1316_; 
lean_inc(v_value_1312_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_value_1312_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1317_, v_x_1318_);
lean_dec(v_x_1318_);
lean_dec(v_a_1317_);
return v_res_1319_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1320_; uint64_t v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1723u);
v___x_1321_ = lean_uint64_of_nat(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_buckets_1324_; lean_object* v___x_1325_; uint64_t v___y_1327_; 
v_buckets_1324_ = lean_ctor_get(v_m_1322_, 1);
v___x_1325_ = lean_array_get_size(v_buckets_1324_);
if (lean_obj_tag(v_a_1323_) == 0)
{
uint64_t v___x_1341_; 
v___x_1341_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1327_ = v___x_1341_;
goto v___jp_1326_;
}
else
{
uint64_t v_hash_1342_; 
v_hash_1342_ = lean_ctor_get_uint64(v_a_1323_, sizeof(void*)*2);
v___y_1327_ = v_hash_1342_;
goto v___jp_1326_;
}
v___jp_1326_:
{
uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v_fold_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1328_ = 32ULL;
v___x_1329_ = lean_uint64_shift_right(v___y_1327_, v___x_1328_);
v_fold_1330_ = lean_uint64_xor(v___y_1327_, v___x_1329_);
v___x_1331_ = 16ULL;
v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
v___x_1335_ = lean_usize_of_nat(v___x_1325_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
v___x_1339_ = lean_array_uget_borrowed(v_buckets_1324_, v___x_1338_);
v___x_1340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1323_, v___x_1339_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_m_1343_);
return v_res_1345_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1349_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1350_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1349_, v___x_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1353_, uint8_t v_isMeta_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v_env_1362_; lean_object* v___y_1364_; lean_object* v___x_1377_; 
v___x_1358_ = lean_st_ref_get(v___y_1356_);
v_env_1362_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_ref(v_env_1362_);
lean_dec(v___x_1358_);
v___x_1377_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1362_, v_declName_1353_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_dec_ref(v_env_1362_);
lean_dec(v_declName_1353_);
goto v___jp_1359_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1379_; lean_object* v_modules_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = l_Lean_Environment_header(v_env_1362_);
v_modules_1380_ = lean_ctor_get(v___x_1379_, 3);
lean_inc_ref(v_modules_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = lean_array_get_size(v_modules_1380_);
v___x_1382_ = lean_nat_dec_lt(v_val_1378_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_modules_1380_);
lean_dec(v_val_1378_);
lean_dec_ref(v_env_1362_);
lean_dec(v_declName_1353_);
goto v___jp_1359_;
}
else
{
lean_object* v___x_1383_; lean_object* v_env_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___y_1388_; 
v___x_1383_ = lean_st_ref_get(v___y_1356_);
v_env_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_env_1384_);
lean_dec(v___x_1383_);
v___x_1385_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1386_ = lean_array_fget(v_modules_1380_, v_val_1378_);
lean_dec(v_val_1378_);
lean_dec_ref(v_modules_1380_);
if (v_isMeta_1354_ == 0)
{
lean_dec_ref(v_env_1384_);
v___y_1388_ = v_isMeta_1354_;
goto v___jp_1387_;
}
else
{
uint8_t v___x_1399_; 
lean_inc(v_declName_1353_);
v___x_1399_ = l_Lean_isMarkedMeta(v_env_1384_, v_declName_1353_);
if (v___x_1399_ == 0)
{
v___y_1388_ = v_isMeta_1354_;
goto v___jp_1387_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = 0;
v___y_1388_ = v___x_1400_;
goto v___jp_1387_;
}
}
v___jp_1387_:
{
lean_object* v_toImport_1389_; lean_object* v_module_1390_; lean_object* v___x_1391_; 
v_toImport_1389_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_ref(v_toImport_1389_);
lean_dec(v___x_1386_);
v_module_1390_ = lean_ctor_get(v_toImport_1389_, 0);
lean_inc(v_module_1390_);
lean_dec_ref(v_toImport_1389_);
lean_inc(v_declName_1353_);
v___x_1391_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1390_, v___y_1388_, v_declName_1353_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1391_);
v___x_1392_ = l_Lean_indirectModUseExt;
v___x_1393_ = lean_box(1);
v___x_1394_ = lean_box(0);
lean_inc_ref(v_env_1362_);
v___x_1395_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1385_, v___x_1392_, v_env_1362_, v___x_1393_, v___x_1394_);
v___x_1396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1395_, v_declName_1353_);
lean_dec(v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1364_ = v___x_1397_;
goto v___jp_1363_;
}
else
{
lean_object* v_val_1398_; 
v_val_1398_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_val_1398_);
lean_dec_ref(v___x_1396_);
v___y_1364_ = v_val_1398_;
goto v___jp_1363_;
}
}
else
{
lean_dec_ref(v_env_1362_);
lean_dec(v_declName_1353_);
return v___x_1391_;
}
}
}
}
v___jp_1359_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
v___jp_1363_:
{
lean_object* v___x_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_box(0);
v_sz_1366_ = lean_array_size(v___y_1364_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1362_, v_declName_1353_, v___y_1364_, v_sz_1366_, v___x_1367_, v___x_1365_, v___y_1355_, v___y_1356_);
lean_dec_ref(v___y_1364_);
lean_dec_ref(v_env_1362_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1368_, 0);
lean_dec(v_unused_1376_);
v___x_1370_ = v___x_1368_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v___x_1368_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1365_);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1365_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1401_, lean_object* v_isMeta_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v_isMeta_boxed_1406_; lean_object* v_res_1407_; 
v_isMeta_boxed_1406_ = lean_unbox(v_isMeta_1402_);
v_res_1407_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1401_, v_isMeta_boxed_1406_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1408_, uint8_t v_x_1409_, lean_object* v_stx_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
lean_inc(v_stx_1410_);
v___x_1414_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1408_, v_stx_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1467_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1467_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1467_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v_env_1420_; uint8_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1419_ = lean_st_ref_get(v___y_1412_);
v_env_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_env_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = 1;
lean_inc(v_a_1415_);
v___x_1422_ = l_Lean_Environment_contains(v_env_1420_, v_a_1415_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; 
lean_dec(v_stx_1410_);
if (v_isShared_1418_ == 0)
{
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1415_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
uint8_t v___x_1426_; lean_object* v___x_1427_; 
lean_del_object(v___x_1417_);
v___x_1426_ = 0;
lean_inc(v_a_1415_);
v___x_1427_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1415_, v___x_1426_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1427_, 0);
lean_dec(v_unused_1458_);
v___x_1429_ = v___x_1427_;
v_isShared_1430_ = v_isSharedCheck_1457_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v___x_1427_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1457_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v_infoState_1432_; uint8_t v_enabled_1433_; 
v___x_1431_ = lean_st_ref_get(v___y_1412_);
v_infoState_1432_ = lean_ctor_get(v___x_1431_, 7);
lean_inc_ref(v_infoState_1432_);
lean_dec(v___x_1431_);
v_enabled_1433_ = lean_ctor_get_uint8(v_infoState_1432_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1432_);
if (v_enabled_1433_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_stx_1410_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_a_1415_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1415_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_del_object(v___x_1429_);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1437_);
lean_dec(v_stx_1410_);
v___x_1439_ = lean_box(0);
lean_inc(v_a_1415_);
v___x_1440_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1438_, v_a_1415_, v___x_1439_, v___y_1411_, v___y_1412_);
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
lean_ctor_set(v___x_1442_, 0, v_a_1415_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1415_);
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
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1415_);
v_a_1449_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1440_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1440_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_a_1415_);
lean_dec(v_stx_1410_);
v_a_1459_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1427_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1427_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1410_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1468_, lean_object* v_x_1469_, lean_object* v_stx_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_x_7364__boxed_1474_; lean_object* v_res_1475_; 
v_x_7364__boxed_1474_ = lean_unbox(v_x_1469_);
v_res_1475_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1468_, v_x_7364__boxed_1474_, v_stx_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1478_, lean_object* v_attrName_1479_, lean_object* v_parserNamespace_1480_, lean_object* v_typeName_1481_, lean_object* v_kind_1482_, lean_object* v_attrDeclName_1483_){
_start:
{
lean_object* v___f_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___f_1485_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1486_, 0, v_parserNamespace_1480_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1488_ = lean_string_append(v_kind_1482_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1489_, 0, v_attrBuiltinName_1478_);
lean_ctor_set(v___x_1489_, 1, v_attrName_1479_);
lean_ctor_set(v___x_1489_, 2, v___x_1488_);
lean_ctor_set(v___x_1489_, 3, v_typeName_1481_);
lean_ctor_set(v___x_1489_, 4, v___f_1486_);
lean_ctor_set(v___x_1489_, 5, v___f_1485_);
v___x_1490_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1489_, v_attrDeclName_1483_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1491_, lean_object* v_attrName_1492_, lean_object* v_parserNamespace_1493_, lean_object* v_typeName_1494_, lean_object* v_kind_1495_, lean_object* v_attrDeclName_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1491_, v_attrName_1492_, v_parserNamespace_1493_, v_typeName_1494_, v_kind_1495_, v_attrDeclName_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1499_, lean_object* v_attrBuiltinName_1500_, lean_object* v_attrName_1501_, lean_object* v_parserNamespace_1502_, lean_object* v_typeName_1503_, lean_object* v_kind_1504_, lean_object* v_attrDeclName_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1500_, v_attrName_1501_, v_parserNamespace_1502_, v_typeName_1503_, v_kind_1504_, v_attrDeclName_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1508_, lean_object* v_attrBuiltinName_1509_, lean_object* v_attrName_1510_, lean_object* v_parserNamespace_1511_, lean_object* v_typeName_1512_, lean_object* v_kind_1513_, lean_object* v_attrDeclName_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1508_, v_attrBuiltinName_1509_, v_attrName_1510_, v_parserNamespace_1511_, v_typeName_1512_, v_kind_1513_, v_attrDeclName_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1517_, lean_object* v_m_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1518_, v_a_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1521_, lean_object* v_m_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1521_, v_m_1522_, v_a_1523_);
lean_dec(v_a_1523_);
lean_dec_ref(v_m_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1525_, v___y_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1536_, v_x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1539_, lean_object* v_x_1540_, lean_object* v_x_1541_){
_start:
{
uint8_t v_res_1542_; lean_object* v_r_1543_; 
v_res_1542_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1539_, v_x_1540_, v_x_1541_);
lean_dec_ref(v_x_1541_);
lean_dec_ref(v_x_1540_);
v_r_1543_ = lean_box(v_res_1542_);
return v_r_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1544_, lean_object* v_a_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1545_, v_x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_a_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1548_, v_a_1549_, v_x_1550_);
lean_dec(v_x_1550_);
lean_dec(v_a_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1552_, lean_object* v_x_1553_, size_t v_x_1554_, lean_object* v_x_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1553_, v_x_1554_, v_x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_){
_start:
{
size_t v_x_7534__boxed_1561_; uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_x_7534__boxed_1561_ = lean_unbox_usize(v_x_1559_);
lean_dec(v_x_1559_);
v_res_1562_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1557_, v_x_1558_, v_x_7534__boxed_1561_, v_x_1560_);
lean_dec_ref(v_x_1560_);
lean_dec_ref(v_x_1558_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1564_, lean_object* v_constName_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1565_, v___y_1566_, v___y_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_constName_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1570_, v_constName_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1576_, lean_object* v_keys_1577_, lean_object* v_vals_1578_, lean_object* v_heq_1579_, lean_object* v_i_1580_, lean_object* v_k_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1577_, v_i_1580_, v_k_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_keys_1584_, lean_object* v_vals_1585_, lean_object* v_heq_1586_, lean_object* v_i_1587_, lean_object* v_k_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1583_, v_keys_1584_, v_vals_1585_, v_heq_1586_, v_i_1587_, v_k_1588_);
lean_dec_ref(v_k_1588_);
lean_dec_ref(v_vals_1585_);
lean_dec_ref(v_keys_1584_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1591_, lean_object* v_ref_1592_, lean_object* v_constName_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1592_, v_constName_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_ref_1599_, lean_object* v_constName_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1598_, v_ref_1599_, v_constName_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_ref_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1605_, lean_object* v_ref_1606_, lean_object* v_msg_1607_, lean_object* v_declHint_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1606_, v_msg_1607_, v_declHint_1608_, v___y_1609_, v___y_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1613_, lean_object* v_ref_1614_, lean_object* v_msg_1615_, lean_object* v_declHint_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1613_, v_ref_1614_, v_msg_1615_, v_declHint_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v_ref_1614_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1621_, lean_object* v_declHint_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1621_, v_declHint_1622_, v___y_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1627_, lean_object* v_declHint_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1627_, v_declHint_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1633_, lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1634_, v_msg_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1640_, lean_object* v_ref_1641_, lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1640_, v_ref_1641_, v_msg_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v_ref_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1660_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1661_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1662_ = lean_box(0);
v___x_1663_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1664_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1659_, v___x_1661_, v___x_1662_, v___x_1663_, v___x_1660_, v_ref_1657_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1675_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1681_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1682_ = l_Lean_addBuiltinDocString(v___x_1680_, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1712_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1713_ = l_Lean_addBuiltinDeclarationRanges(v___x_1711_, v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1716_, lean_object* v_a_1717_, lean_object* v_____r_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_declName_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1732_; 
v_declName_1721_ = lean_ctor_get(v_toOLeanEntry_1716_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_toOLeanEntry_1716_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v_toOLeanEntry_1716_, 0);
lean_dec(v_unused_1733_);
v___x_1723_ = v_toOLeanEntry_1716_;
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_declName_1721_);
lean_dec(v_toOLeanEntry_1716_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1717_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1725_);
lean_ctor_set(v___x_1723_, 0, v_declName_1721_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_declName_1721_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___y_1720_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1734_, lean_object* v_a_1735_, lean_object* v_____r_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1734_, v_a_1735_, v_____r_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1743_, lean_object* v_as_x27_1744_, lean_object* v_b_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
if (lean_obj_tag(v_as_x27_1744_) == 0)
{
lean_object* v___x_1748_; 
lean_dec(v_stx_1743_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_b_1745_);
lean_ctor_set(v___x_1748_, 1, v___y_1747_);
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; lean_object* v_toOLeanEntry_1751_; uint8_t v_isBuiltin_1752_; lean_object* v_value_1753_; lean_object* v_macroScope_1754_; lean_object* v_traceMsgs_1755_; lean_object* v_expandedMacroDecls_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_b_1745_);
v_head_1749_ = lean_ctor_get(v_as_x27_1744_, 0);
v_tail_1750_ = lean_ctor_get(v_as_x27_1744_, 1);
v_toOLeanEntry_1751_ = lean_ctor_get(v_head_1749_, 0);
v_isBuiltin_1752_ = lean_ctor_get_uint8(v_head_1749_, sizeof(void*)*2);
v_value_1753_ = lean_ctor_get(v_head_1749_, 1);
v_macroScope_1754_ = lean_ctor_get(v___y_1747_, 0);
v_traceMsgs_1755_ = lean_ctor_get(v___y_1747_, 1);
v_expandedMacroDecls_1756_ = lean_ctor_get(v___y_1747_, 2);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___y_1747_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1758_ = v___y_1747_;
v_isShared_1759_ = v_isSharedCheck_1821_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_expandedMacroDecls_1756_);
lean_inc(v_traceMsgs_1755_);
lean_inc(v_macroScope_1754_);
lean_dec(v___y_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1821_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_methods_1760_; lean_object* v_quotContext_1761_; lean_object* v_currRecDepth_1762_; lean_object* v_maxRecDepth_1763_; lean_object* v_ref_1764_; lean_object* v___x_1765_; lean_object* v_a_1767_; lean_object* v_a_1768_; lean_object* v___x_1772_; lean_object* v_a_1774_; lean_object* v_a_1775_; lean_object* v___y_1782_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
v_methods_1760_ = lean_ctor_get(v___y_1746_, 0);
v_quotContext_1761_ = lean_ctor_get(v___y_1746_, 1);
v_currRecDepth_1762_ = lean_ctor_get(v___y_1746_, 3);
v_maxRecDepth_1763_ = lean_ctor_get(v___y_1746_, 4);
v_ref_1764_ = lean_ctor_get(v___y_1746_, 5);
v___x_1765_ = lean_box(0);
v___x_1772_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1788_ = lean_unsigned_to_nat(1u);
v___x_1789_ = lean_nat_add(v_macroScope_1754_, v___x_1788_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1789_);
v___x_1791_ = v___x_1758_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_traceMsgs_1755_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_expandedMacroDecls_1756_);
v___x_1791_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1790_;
}
v___jp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1767_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v___x_1765_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_a_1768_);
return v___x_1771_;
}
v___jp_1773_:
{
if (lean_obj_tag(v_a_1774_) == 1)
{
v_as_x27_1744_ = v_tail_1750_;
v_b_1745_ = v___x_1772_;
v___y_1747_ = v_a_1775_;
goto _start;
}
else
{
lean_object* v_declName_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_stx_1743_);
v_declName_1777_ = lean_ctor_get(v_toOLeanEntry_1751_, 1);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1774_);
lean_inc(v_declName_1777_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_declName_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
v_a_1767_ = v___x_1780_;
v_a_1768_ = v_a_1775_;
goto v___jp_1766_;
}
}
v___jp_1781_:
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___y_1782_, 0);
if (lean_obj_tag(v_a_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v_a_1785_; 
lean_inc_ref(v_a_1783_);
lean_dec(v_stx_1743_);
v_a_1784_ = lean_ctor_get(v___y_1782_, 1);
lean_inc(v_a_1784_);
lean_dec_ref(v___y_1782_);
v_a_1785_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v_a_1783_);
v_a_1767_ = v_a_1785_;
v_a_1768_ = v_a_1784_;
goto v___jp_1766_;
}
else
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___y_1782_, 1);
lean_inc(v_a_1786_);
lean_dec_ref(v___y_1782_);
v_as_x27_1744_ = v_tail_1750_;
v_b_1745_ = v___x_1772_;
v___y_1747_ = v_a_1786_;
goto _start;
}
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_inc(v_ref_1764_);
lean_inc(v_maxRecDepth_1763_);
lean_inc(v_currRecDepth_1762_);
lean_inc(v_quotContext_1761_);
lean_inc(v_methods_1760_);
v___x_1792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1792_, 0, v_methods_1760_);
lean_ctor_set(v___x_1792_, 1, v_quotContext_1761_);
lean_ctor_set(v___x_1792_, 2, v_macroScope_1754_);
lean_ctor_set(v___x_1792_, 3, v_currRecDepth_1762_);
lean_ctor_set(v___x_1792_, 4, v_maxRecDepth_1763_);
lean_ctor_set(v___x_1792_, 5, v_ref_1764_);
lean_inc(v_value_1753_);
lean_inc(v_stx_1743_);
v___x_1793_ = lean_apply_3(v_value_1753_, v_stx_1743_, v___x_1792_, v___x_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
if (v_isBuiltin_1752_ == 0)
{
lean_object* v_a_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1814_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 1);
v_a_1795_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1797_ = v___x_1793_;
v_isShared_1798_ = v_isSharedCheck_1814_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1794_);
lean_inc(v_a_1795_);
lean_dec(v___x_1793_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1814_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_macroScope_1799_; lean_object* v_traceMsgs_1800_; lean_object* v_expandedMacroDecls_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1813_; 
v_macroScope_1799_ = lean_ctor_get(v_a_1794_, 0);
v_traceMsgs_1800_ = lean_ctor_get(v_a_1794_, 1);
v_expandedMacroDecls_1801_ = lean_ctor_get(v_a_1794_, 2);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1794_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1803_ = v_a_1794_;
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_expandedMacroDecls_1801_);
lean_inc(v_traceMsgs_1800_);
lean_inc(v_macroScope_1799_);
lean_dec(v_a_1794_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_declName_1805_; lean_object* v___x_1807_; 
v_declName_1805_ = lean_ctor_get(v_toOLeanEntry_1751_, 1);
lean_inc(v_declName_1805_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
lean_ctor_set(v___x_1797_, 1, v_expandedMacroDecls_1801_);
lean_ctor_set(v___x_1797_, 0, v_declName_1805_);
v___x_1807_ = v___x_1797_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_declName_1805_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_expandedMacroDecls_1801_);
v___x_1807_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 2, v___x_1807_);
v___x_1809_ = v___x_1803_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_macroScope_1799_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_traceMsgs_1800_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; 
lean_inc_ref(v_toOLeanEntry_1751_);
v___x_1810_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1751_, v_a_1795_, v___x_1765_, v___y_1746_, v___x_1809_);
v___y_1782_ = v___x_1810_;
goto v___jp_1781_;
}
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1815_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1815_);
v_a_1816_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1793_);
lean_inc_ref(v_toOLeanEntry_1751_);
v___x_1817_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1751_, v_a_1815_, v___x_1765_, v___y_1746_, v_a_1816_);
v___y_1782_ = v___x_1817_;
goto v___jp_1781_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v_a_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1818_);
v_a_1819_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1793_);
v_a_1774_ = v_a_1818_;
v_a_1775_ = v_a_1819_;
goto v___jp_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1822_, v_as_x27_1823_, v_b_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_as_x27_1823_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1828_, lean_object* v_stx_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; lean_object* v_fst_1839_; 
v___x_1832_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1829_);
v___x_1833_ = l_Lean_Syntax_getKind(v_stx_1829_);
v___x_1834_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1832_, v_env_1828_, v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = lean_box(0);
v___x_1836_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1837_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1829_, v___x_1834_, v___x_1836_, v_a_1830_, v_a_1831_);
lean_dec(v___x_1834_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
v_fst_1839_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_fst_1839_);
lean_dec(v_a_1838_);
if (lean_obj_tag(v_fst_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1837_, 0);
lean_dec(v_unused_1848_);
v___x_1842_ = v___x_1837_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1837_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1835_);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_a_1849_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1837_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1837_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1837_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_val_1853_; lean_object* v___x_1855_; 
v_val_1853_ = lean_ctor_get(v_fst_1839_, 0);
lean_inc(v_val_1853_);
lean_dec_ref(v_fst_1839_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_val_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_val_1853_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_a_1849_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1859_, lean_object* v_stx_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1859_, v_stx_1860_, v_a_1861_, v_a_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1864_, lean_object* v_as_1865_, lean_object* v_as_x27_1866_, lean_object* v_b_1867_, lean_object* v_a_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1864_, v_as_x27_1866_, v_b_1867_, v___y_1869_, v___y_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1872_, lean_object* v_as_1873_, lean_object* v_as_x27_1874_, lean_object* v_b_1875_, lean_object* v_a_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1872_, v_as_1873_, v_as_x27_1874_, v_b_1875_, v_a_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v_as_x27_1874_);
lean_dec(v_as_1873_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1880_, lean_object* v_inst_1881_, lean_object* v_s_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_apply_1(v_setNextMacroScope_1880_, v_s_1882_);
v___x_1884_ = lean_apply_2(v_inst_1881_, lean_box(0), v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_){
_start:
{
lean_object* v_getNextMacroScope_1888_; lean_object* v_setNextMacroScope_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1898_; 
v_getNextMacroScope_1888_ = lean_ctor_get(v_inst_1887_, 1);
v_setNextMacroScope_1889_ = lean_ctor_get(v_inst_1887_, 2);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_inst_1887_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_inst_1887_, 0);
lean_dec(v_unused_1899_);
v___x_1891_ = v_inst_1887_;
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_setNextMacroScope_1889_);
lean_inc(v_getNextMacroScope_1888_);
lean_dec(v_inst_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_inc(v_inst_1885_);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1893_, 0, v_setNextMacroScope_1889_);
lean_closure_set(v___f_1893_, 1, v_inst_1885_);
v___x_1894_ = lean_apply_2(v_inst_1885_, lean_box(0), v_getNextMacroScope_1888_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v___f_1893_);
lean_ctor_set(v___x_1891_, 1, v___x_1894_);
lean_ctor_set(v___x_1891_, 0, v_inst_1886_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_inst_1886_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___f_1893_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1900_, lean_object* v_n_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_){
_start:
{
lean_object* v_getNextMacroScope_1905_; lean_object* v_setNextMacroScope_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1915_; 
v_getNextMacroScope_1905_ = lean_ctor_get(v_inst_1904_, 1);
v_setNextMacroScope_1906_ = lean_ctor_get(v_inst_1904_, 2);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_inst_1904_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_inst_1904_, 0);
lean_dec(v_unused_1916_);
v___x_1908_ = v_inst_1904_;
v_isShared_1909_ = v_isSharedCheck_1915_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_setNextMacroScope_1906_);
lean_inc(v_getNextMacroScope_1905_);
lean_dec(v_inst_1904_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1915_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_inc(v_inst_1902_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1910_, 0, v_setNextMacroScope_1906_);
lean_closure_set(v___f_1910_, 1, v_inst_1902_);
v___x_1911_ = lean_apply_2(v_inst_1902_, lean_box(0), v_getNextMacroScope_1905_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 2, v___f_1910_);
lean_ctor_set(v___x_1908_, 1, v___x_1911_);
lean_ctor_set(v___x_1908_, 0, v_inst_1903_);
v___x_1913_ = v___x_1908_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_inst_1903_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v___f_1910_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1917_, lean_object* v_snd_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_toMonadRef_1921_, lean_object* v_inst_1922_, lean_object* v_fst_1923_, uint8_t v_____do__lift_1924_){
_start:
{
if (v_____do__lift_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec(v_fst_1923_);
lean_dec(v_inst_1922_);
lean_dec_ref(v_toMonadRef_1921_);
lean_dec_ref(v_inst_1920_);
lean_dec_ref(v_inst_1919_);
lean_dec_ref(v_snd_1918_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_apply_2(v_toPure_1917_, lean_box(0), v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_toPure_1917_);
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_snd_1918_);
v___x_1928_ = l_Lean_MessageData_ofFormat(v___x_1927_);
v___x_1929_ = l_Lean_addTrace___redArg(v_inst_1919_, v_inst_1920_, v_toMonadRef_1921_, v_inst_1922_, v_fst_1923_, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1930_, lean_object* v_snd_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_toMonadRef_1934_, lean_object* v_inst_1935_, lean_object* v_fst_1936_, lean_object* v_____do__lift_1937_){
_start:
{
uint8_t v_____do__lift_1416__boxed_1938_; lean_object* v_res_1939_; 
v_____do__lift_1416__boxed_1938_ = lean_unbox(v_____do__lift_1937_);
v_res_1939_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1930_, v_snd_1931_, v_inst_1932_, v_inst_1933_, v_toMonadRef_1934_, v_inst_1935_, v_fst_1936_, v_____do__lift_1416__boxed_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1940_, lean_object* v_fst_1941_, lean_object* v_____do__lift_1942_, lean_object* v_____do__lift_1943_){
_start:
{
uint8_t v_hasTrace_1944_; 
v_hasTrace_1944_ = lean_ctor_get_uint8(v_____do__lift_1943_, sizeof(void*)*1);
if (v_hasTrace_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec(v_fst_1941_);
v___x_1945_ = lean_box(v_hasTrace_1944_);
v___x_1946_ = lean_apply_2(v_toPure_1940_, lean_box(0), v___x_1945_);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1948_ = l_Lean_Name_append(v___x_1947_, v_fst_1941_);
v___x_1949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1942_, v_____do__lift_1943_, v___x_1948_);
lean_dec(v___x_1948_);
v___x_1950_ = lean_box(v___x_1949_);
v___x_1951_ = lean_apply_2(v_toPure_1940_, lean_box(0), v___x_1950_);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(lean_object* v_toPure_1952_, lean_object* v_fst_1953_, lean_object* v_____do__lift_1954_, lean_object* v_____do__lift_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Elab_liftMacroM___redArg___lam__1(v_toPure_1952_, v_fst_1953_, v_____do__lift_1954_, v_____do__lift_1955_);
lean_dec_ref(v_____do__lift_1955_);
lean_dec_ref(v_____do__lift_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1957_, lean_object* v_fst_1958_, lean_object* v_toBind_1959_, lean_object* v_inst_1960_, lean_object* v_____do__lift_1961_){
_start:
{
lean_object* v___f_1962_; lean_object* v___x_1963_; 
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1962_, 0, v_toPure_1957_);
lean_closure_set(v___f_1962_, 1, v_fst_1958_);
lean_closure_set(v___f_1962_, 2, v_____do__lift_1961_);
v___x_1963_ = lean_apply_4(v_toBind_1959_, lean_box(0), lean_box(0), v_inst_1960_, v___f_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1964_, lean_object* v_toPure_1965_, lean_object* v_inst_1966_, lean_object* v_toMonadRef_1967_, lean_object* v_inst_1968_, lean_object* v_toBind_1969_, lean_object* v_inst_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v_getInheritedTraceOptions_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_fst_1972_ = lean_ctor_get(v_x_1971_, 0);
lean_inc_n(v_fst_1972_, 2);
v_snd_1973_ = lean_ctor_get(v_x_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v_x_1971_);
v_getInheritedTraceOptions_1974_ = lean_ctor_get(v_inst_1964_, 2);
lean_inc(v_getInheritedTraceOptions_1974_);
lean_inc(v_toPure_1965_);
v___f_1975_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1975_, 0, v_toPure_1965_);
lean_closure_set(v___f_1975_, 1, v_snd_1973_);
lean_closure_set(v___f_1975_, 2, v_inst_1966_);
lean_closure_set(v___f_1975_, 3, v_inst_1964_);
lean_closure_set(v___f_1975_, 4, v_toMonadRef_1967_);
lean_closure_set(v___f_1975_, 5, v_inst_1968_);
lean_closure_set(v___f_1975_, 6, v_fst_1972_);
lean_inc_n(v_toBind_1969_, 2);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1976_, 0, v_toPure_1965_);
lean_closure_set(v___f_1976_, 1, v_fst_1972_);
lean_closure_set(v___f_1976_, 2, v_toBind_1969_);
lean_closure_set(v___f_1976_, 3, v_inst_1970_);
v___x_1977_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1974_, v___f_1976_);
v___x_1978_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1977_, v___f_1975_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_1979_, lean_object* v___x_1980_, lean_object* v___x_1981_, lean_object* v_stx_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1979_, v_stx_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
if (lean_obj_tag(v_a_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v___x_1981_);
lean_dec_ref(v___x_1980_);
v_a_1987_ = lean_ctor_get(v___x_1985_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1985_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v___x_1985_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1991_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1987_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2027_; 
v_val_1997_ = lean_ctor_get(v_a_1986_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_1986_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1999_ = v_a_1986_;
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_val_1997_);
lean_dec(v_a_1986_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_snd_2001_; 
v_snd_2001_ = lean_ctor_get(v_val_1997_, 1);
lean_inc(v_snd_2001_);
lean_dec(v_val_1997_);
if (lean_obj_tag(v_snd_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2012_; 
lean_del_object(v___x_1999_);
v_a_2002_ = lean_ctor_get(v___x_1985_, 1);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_1985_);
v_a_2003_ = lean_ctor_get(v_snd_2001_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_snd_2001_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2005_ = v_snd_2001_;
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v_snd_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_1195__overap_2009_; lean_object* v___x_2010_; 
v___x_1195__overap_2009_ = l_liftExcept___redArg(v___x_1980_, v___x_1981_, v___x_2008_);
lean_inc_ref(v___y_1983_);
v___x_2010_ = lean_apply_2(v___x_1195__overap_2009_, v___y_1983_, v_a_2002_);
return v___x_2010_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2026_; 
v_a_2013_ = lean_ctor_get(v___x_1985_, 1);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_1985_);
v_a_2014_ = lean_ctor_get(v_snd_2001_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_snd_2001_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2016_ = v_snd_2001_;
v_isShared_2017_ = v_isSharedCheck_2026_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v_snd_2001_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2026_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v_a_2014_);
v___x_2019_ = v___x_1999_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2019_);
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_1199__overap_2022_; lean_object* v___x_2023_; 
v___x_1199__overap_2022_ = l_liftExcept___redArg(v___x_1980_, v___x_1981_, v___x_2021_);
lean_inc_ref(v___y_1983_);
v___x_2023_ = lean_apply_2(v___x_1199__overap_2022_, v___y_1983_, v_a_2013_);
return v___x_2023_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_1981_);
lean_dec_ref(v___x_1980_);
v_a_2028_ = lean_ctor_get(v___x_1985_, 0);
v_a_2029_ = lean_ctor_get(v___x_1985_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1985_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_inc(v_a_2028_);
lean_dec(v___x_1985_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2037_, lean_object* v___x_2038_, lean_object* v___x_2039_, lean_object* v_stx_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2037_, v___x_2038_, v___x_2039_, v_stx_2040_, v___y_2041_, v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2044_, lean_object* v_declName_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2048_; lean_object* v_env_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; uint8_t v___x_2052_; 
v___x_2048_ = 0;
v_env_2049_ = l_Lean_Environment_setExporting(v_env_2044_, v___x_2048_);
lean_inc(v_declName_2045_);
v___x_2050_ = l_Lean_mkPrivateName(v_env_2049_, v_declName_2045_);
v___x_2051_ = 1;
lean_inc_ref(v_env_2049_);
v___x_2052_ = l_Lean_Environment_contains(v_env_2049_, v___x_2050_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2053_ = l_Lean_privateToUserName(v_declName_2045_);
v___x_2054_ = l_Lean_Environment_contains(v_env_2049_, v___x_2053_, v___x_2051_);
v___x_2055_ = lean_box(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___y_2047_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v_env_2049_);
lean_dec(v_declName_2045_);
v___x_2057_ = lean_box(v___x_2052_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___y_2047_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2059_, lean_object* v_declName_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2059_, v_declName_2060_, v___y_2061_, v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2064_, lean_object* v_currNamespace_2065_, lean_object* v_openDecls_2066_, lean_object* v_n_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = l_Lean_ResolveName_resolveNamespace(v_env_2064_, v_currNamespace_2065_, v_openDecls_2066_, v_n_2067_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2072_, lean_object* v_currNamespace_2073_, lean_object* v_openDecls_2074_, lean_object* v_n_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2072_, v_currNamespace_2073_, v_openDecls_2074_, v_n_2075_, v___y_2076_, v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2079_, lean_object* v_opts_2080_, lean_object* v_currNamespace_2081_, lean_object* v_openDecls_2082_, lean_object* v_n_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = l_Lean_ResolveName_resolveGlobalName(v_env_2079_, v_opts_2080_, v_currNamespace_2081_, v_openDecls_2082_, v_n_2083_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2088_, lean_object* v_opts_2089_, lean_object* v_currNamespace_2090_, lean_object* v_openDecls_2091_, lean_object* v_n_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2088_, v_opts_2089_, v_currNamespace_2090_, v_openDecls_2091_, v_n_2092_, v___y_2093_, v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec_ref(v_opts_2089_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2096_, lean_object* v_a_2097_, lean_object* v_____r_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_apply_2(v_toPure_2096_, lean_box(0), v_a_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2100_, lean_object* v_inst_2101_, lean_object* v___f_2102_, lean_object* v_toBind_2103_, lean_object* v___f_2104_, lean_object* v_____r_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = l_List_reverse___redArg(v_traceMsgs_2100_);
v___x_2107_ = l_List_forM___redArg(v_inst_2101_, v___x_2106_, v___f_2102_);
v___x_2108_ = lean_apply_4(v_toBind_2103_, lean_box(0), lean_box(0), v___x_2107_, v___f_2104_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2109_, lean_object* v_macroScope_2110_, lean_object* v_toBind_2111_, lean_object* v___f_2112_, lean_object* v_____s_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_apply_1(v_setNextMacroScope_2109_, v_macroScope_2110_);
v___x_2115_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2114_, v___f_2112_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2116_, lean_object* v_toPure_2117_, lean_object* v_____r_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
v___x_2120_ = lean_apply_2(v_toPure_2117_, lean_box(0), v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_toMonadRef_2125_, lean_object* v_inst_2126_, lean_object* v_toBind_2127_, lean_object* v___f_2128_, lean_object* v_a_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = 1;
v___x_2133_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2121_, v_inst_2122_, v_inst_2123_, v_inst_2124_, v_toMonadRef_2125_, v_inst_2126_, v_a_2129_, v___x_2132_);
v___x_2134_ = lean_apply_4(v_toBind_2127_, lean_box(0), lean_box(0), v___x_2133_, v___f_2128_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2136_, lean_object* v_____do__lift_2137_, lean_object* v_____do__lift_2138_, lean_object* v_____do__lift_2139_, lean_object* v_____do__lift_2140_, lean_object* v_____do__lift_2141_, lean_object* v_x_2142_, lean_object* v_toPure_2143_, lean_object* v_inst_2144_, lean_object* v___f_2145_, lean_object* v_toBind_2146_, lean_object* v_setNextMacroScope_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_toMonadRef_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_toMonadExceptOf_2154_, lean_object* v_____do__lift_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2156_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2156_, 0, v_methods_2136_);
lean_ctor_set(v___x_2156_, 1, v_____do__lift_2137_);
lean_ctor_set(v___x_2156_, 2, v_____do__lift_2138_);
lean_ctor_set(v___x_2156_, 3, v_____do__lift_2139_);
lean_ctor_set(v___x_2156_, 4, v_____do__lift_2140_);
lean_ctor_set(v___x_2156_, 5, v_____do__lift_2141_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2158_, 0, v_____do__lift_2155_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
lean_ctor_set(v___x_2158_, 2, v___x_2157_);
v___x_2159_ = lean_apply_2(v_x_2142_, v___x_2156_, v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v_a_2161_; lean_object* v_macroScope_2162_; lean_object* v_traceMsgs_2163_; lean_object* v_expandedMacroDecls_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v_toMonadExceptOf_2154_);
lean_dec_ref(v_inst_2153_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 1);
lean_inc(v_a_2160_);
v_a_2161_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2159_);
v_macroScope_2162_ = lean_ctor_get(v_a_2160_, 0);
lean_inc(v_macroScope_2162_);
v_traceMsgs_2163_ = lean_ctor_get(v_a_2160_, 1);
lean_inc(v_traceMsgs_2163_);
v_expandedMacroDecls_2164_ = lean_ctor_get(v_a_2160_, 2);
lean_inc(v_expandedMacroDecls_2164_);
lean_dec(v_a_2160_);
lean_inc(v_toPure_2143_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2165_, 0, v_toPure_2143_);
lean_closure_set(v___f_2165_, 1, v_a_2161_);
lean_inc_n(v_toBind_2146_, 3);
lean_inc_ref_n(v_inst_2144_, 2);
v___f_2166_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2166_, 0, v_traceMsgs_2163_);
lean_closure_set(v___f_2166_, 1, v_inst_2144_);
lean_closure_set(v___f_2166_, 2, v___f_2145_);
lean_closure_set(v___f_2166_, 3, v_toBind_2146_);
lean_closure_set(v___f_2166_, 4, v___f_2165_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2167_, 0, v_setNextMacroScope_2147_);
lean_closure_set(v___f_2167_, 1, v_macroScope_2162_);
lean_closure_set(v___f_2167_, 2, v_toBind_2146_);
lean_closure_set(v___f_2167_, 3, v___f_2166_);
v___x_2168_ = lean_box(0);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2169_, 0, v___x_2168_);
lean_closure_set(v___f_2169_, 1, v_toPure_2143_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2170_, 0, v_inst_2144_);
lean_closure_set(v___f_2170_, 1, v_inst_2148_);
lean_closure_set(v___f_2170_, 2, v_inst_2149_);
lean_closure_set(v___f_2170_, 3, v_inst_2150_);
lean_closure_set(v___f_2170_, 4, v_toMonadRef_2151_);
lean_closure_set(v___f_2170_, 5, v_inst_2152_);
lean_closure_set(v___f_2170_, 6, v_toBind_2146_);
lean_closure_set(v___f_2170_, 7, v___f_2169_);
v___x_2171_ = l_List_forIn_x27_loop___redArg(v_inst_2144_, v___f_2170_, v_expandedMacroDecls_2164_, v___x_2168_);
lean_dec(v_expandedMacroDecls_2164_);
v___x_2172_ = lean_apply_4(v_toBind_2146_, lean_box(0), lean_box(0), v___x_2171_, v___f_2167_);
return v___x_2172_;
}
else
{
lean_object* v_a_2173_; 
lean_dec(v_inst_2152_);
lean_dec_ref(v_toMonadRef_2151_);
lean_dec(v_inst_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_inst_2148_);
lean_dec(v_setNextMacroScope_2147_);
lean_dec(v_toBind_2146_);
lean_dec(v___f_2145_);
lean_dec(v_toPure_2143_);
v_a_2173_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2173_);
lean_dec_ref(v___x_2159_);
if (lean_obj_tag(v_a_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_a_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
lean_dec_ref(v_toMonadExceptOf_2154_);
v_a_2174_ = lean_ctor_get(v_a_2173_, 0);
lean_inc(v_a_2174_);
v_a_2175_ = lean_ctor_get(v_a_2173_, 1);
lean_inc_ref(v_a_2175_);
lean_dec_ref(v_a_2173_);
v___x_2176_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2177_ = lean_string_dec_eq(v_a_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_a_2175_);
v___x_2179_ = l_Lean_MessageData_ofFormat(v___x_2178_);
v___x_2180_ = l_Lean_throwErrorAt___redArg(v_inst_2144_, v_inst_2153_, v_a_2174_, v___x_2179_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; 
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_inst_2144_);
v___x_2181_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2153_, v_a_2174_);
return v___x_2181_;
}
}
else
{
lean_object* v___x_2182_; 
lean_dec_ref(v_inst_2153_);
lean_dec_ref(v_inst_2144_);
v___x_2182_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2154_);
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2183_ = _args[0];
lean_object* v_____do__lift_2184_ = _args[1];
lean_object* v_____do__lift_2185_ = _args[2];
lean_object* v_____do__lift_2186_ = _args[3];
lean_object* v_____do__lift_2187_ = _args[4];
lean_object* v_____do__lift_2188_ = _args[5];
lean_object* v_x_2189_ = _args[6];
lean_object* v_toPure_2190_ = _args[7];
lean_object* v_inst_2191_ = _args[8];
lean_object* v___f_2192_ = _args[9];
lean_object* v_toBind_2193_ = _args[10];
lean_object* v_setNextMacroScope_2194_ = _args[11];
lean_object* v_inst_2195_ = _args[12];
lean_object* v_inst_2196_ = _args[13];
lean_object* v_inst_2197_ = _args[14];
lean_object* v_toMonadRef_2198_ = _args[15];
lean_object* v_inst_2199_ = _args[16];
lean_object* v_inst_2200_ = _args[17];
lean_object* v_toMonadExceptOf_2201_ = _args[18];
lean_object* v_____do__lift_2202_ = _args[19];
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2183_, v_____do__lift_2184_, v_____do__lift_2185_, v_____do__lift_2186_, v_____do__lift_2187_, v_____do__lift_2188_, v_x_2189_, v_toPure_2190_, v_inst_2191_, v___f_2192_, v_toBind_2193_, v_setNextMacroScope_2194_, v_inst_2195_, v_inst_2196_, v_inst_2197_, v_toMonadRef_2198_, v_inst_2199_, v_inst_2200_, v_toMonadExceptOf_2201_, v_____do__lift_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2204_, lean_object* v_____do__lift_2205_, lean_object* v_____do__lift_2206_, lean_object* v_____do__lift_2207_, lean_object* v_____do__lift_2208_, lean_object* v_x_2209_, lean_object* v_toPure_2210_, lean_object* v_inst_2211_, lean_object* v___f_2212_, lean_object* v_toBind_2213_, lean_object* v_setNextMacroScope_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_toMonadRef_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_toMonadExceptOf_2221_, lean_object* v_getNextMacroScope_2222_, lean_object* v_____do__lift_2223_){
_start:
{
lean_object* v___f_2224_; lean_object* v___x_2225_; 
lean_inc(v_toBind_2213_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2224_, 0, v_methods_2204_);
lean_closure_set(v___f_2224_, 1, v_____do__lift_2205_);
lean_closure_set(v___f_2224_, 2, v_____do__lift_2206_);
lean_closure_set(v___f_2224_, 3, v_____do__lift_2207_);
lean_closure_set(v___f_2224_, 4, v_____do__lift_2223_);
lean_closure_set(v___f_2224_, 5, v_____do__lift_2208_);
lean_closure_set(v___f_2224_, 6, v_x_2209_);
lean_closure_set(v___f_2224_, 7, v_toPure_2210_);
lean_closure_set(v___f_2224_, 8, v_inst_2211_);
lean_closure_set(v___f_2224_, 9, v___f_2212_);
lean_closure_set(v___f_2224_, 10, v_toBind_2213_);
lean_closure_set(v___f_2224_, 11, v_setNextMacroScope_2214_);
lean_closure_set(v___f_2224_, 12, v_inst_2215_);
lean_closure_set(v___f_2224_, 13, v_inst_2216_);
lean_closure_set(v___f_2224_, 14, v_inst_2217_);
lean_closure_set(v___f_2224_, 15, v_toMonadRef_2218_);
lean_closure_set(v___f_2224_, 16, v_inst_2219_);
lean_closure_set(v___f_2224_, 17, v_inst_2220_);
lean_closure_set(v___f_2224_, 18, v_toMonadExceptOf_2221_);
v___x_2225_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v_getNextMacroScope_2222_, v___f_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2226_ = _args[0];
lean_object* v_____do__lift_2227_ = _args[1];
lean_object* v_____do__lift_2228_ = _args[2];
lean_object* v_____do__lift_2229_ = _args[3];
lean_object* v_____do__lift_2230_ = _args[4];
lean_object* v_x_2231_ = _args[5];
lean_object* v_toPure_2232_ = _args[6];
lean_object* v_inst_2233_ = _args[7];
lean_object* v___f_2234_ = _args[8];
lean_object* v_toBind_2235_ = _args[9];
lean_object* v_setNextMacroScope_2236_ = _args[10];
lean_object* v_inst_2237_ = _args[11];
lean_object* v_inst_2238_ = _args[12];
lean_object* v_inst_2239_ = _args[13];
lean_object* v_toMonadRef_2240_ = _args[14];
lean_object* v_inst_2241_ = _args[15];
lean_object* v_inst_2242_ = _args[16];
lean_object* v_toMonadExceptOf_2243_ = _args[17];
lean_object* v_getNextMacroScope_2244_ = _args[18];
lean_object* v_____do__lift_2245_ = _args[19];
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2226_, v_____do__lift_2227_, v_____do__lift_2228_, v_____do__lift_2229_, v_____do__lift_2230_, v_x_2231_, v_toPure_2232_, v_inst_2233_, v___f_2234_, v_toBind_2235_, v_setNextMacroScope_2236_, v_inst_2237_, v_inst_2238_, v_inst_2239_, v_toMonadRef_2240_, v_inst_2241_, v_inst_2242_, v_toMonadExceptOf_2243_, v_getNextMacroScope_2244_, v_____do__lift_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2247_, lean_object* v_____do__lift_2248_, lean_object* v_____do__lift_2249_, lean_object* v_____do__lift_2250_, lean_object* v_x_2251_, lean_object* v_toPure_2252_, lean_object* v_inst_2253_, lean_object* v___f_2254_, lean_object* v_toBind_2255_, lean_object* v_setNextMacroScope_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_toMonadRef_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_toMonadExceptOf_2263_, lean_object* v_getNextMacroScope_2264_, lean_object* v_getMaxRecDepth_2265_, lean_object* v_____do__lift_2266_){
_start:
{
lean_object* v___f_2267_; lean_object* v___x_2268_; 
lean_inc(v_toBind_2255_);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2267_, 0, v_methods_2247_);
lean_closure_set(v___f_2267_, 1, v_____do__lift_2248_);
lean_closure_set(v___f_2267_, 2, v_____do__lift_2249_);
lean_closure_set(v___f_2267_, 3, v_____do__lift_2266_);
lean_closure_set(v___f_2267_, 4, v_____do__lift_2250_);
lean_closure_set(v___f_2267_, 5, v_x_2251_);
lean_closure_set(v___f_2267_, 6, v_toPure_2252_);
lean_closure_set(v___f_2267_, 7, v_inst_2253_);
lean_closure_set(v___f_2267_, 8, v___f_2254_);
lean_closure_set(v___f_2267_, 9, v_toBind_2255_);
lean_closure_set(v___f_2267_, 10, v_setNextMacroScope_2256_);
lean_closure_set(v___f_2267_, 11, v_inst_2257_);
lean_closure_set(v___f_2267_, 12, v_inst_2258_);
lean_closure_set(v___f_2267_, 13, v_inst_2259_);
lean_closure_set(v___f_2267_, 14, v_toMonadRef_2260_);
lean_closure_set(v___f_2267_, 15, v_inst_2261_);
lean_closure_set(v___f_2267_, 16, v_inst_2262_);
lean_closure_set(v___f_2267_, 17, v_toMonadExceptOf_2263_);
lean_closure_set(v___f_2267_, 18, v_getNextMacroScope_2264_);
v___x_2268_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v_getMaxRecDepth_2265_, v___f_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2269_ = _args[0];
lean_object* v_____do__lift_2270_ = _args[1];
lean_object* v_____do__lift_2271_ = _args[2];
lean_object* v_____do__lift_2272_ = _args[3];
lean_object* v_x_2273_ = _args[4];
lean_object* v_toPure_2274_ = _args[5];
lean_object* v_inst_2275_ = _args[6];
lean_object* v___f_2276_ = _args[7];
lean_object* v_toBind_2277_ = _args[8];
lean_object* v_setNextMacroScope_2278_ = _args[9];
lean_object* v_inst_2279_ = _args[10];
lean_object* v_inst_2280_ = _args[11];
lean_object* v_inst_2281_ = _args[12];
lean_object* v_toMonadRef_2282_ = _args[13];
lean_object* v_inst_2283_ = _args[14];
lean_object* v_inst_2284_ = _args[15];
lean_object* v_toMonadExceptOf_2285_ = _args[16];
lean_object* v_getNextMacroScope_2286_ = _args[17];
lean_object* v_getMaxRecDepth_2287_ = _args[18];
lean_object* v_____do__lift_2288_ = _args[19];
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2269_, v_____do__lift_2270_, v_____do__lift_2271_, v_____do__lift_2272_, v_x_2273_, v_toPure_2274_, v_inst_2275_, v___f_2276_, v_toBind_2277_, v_setNextMacroScope_2278_, v_inst_2279_, v_inst_2280_, v_inst_2281_, v_toMonadRef_2282_, v_inst_2283_, v_inst_2284_, v_toMonadExceptOf_2285_, v_getNextMacroScope_2286_, v_getMaxRecDepth_2287_, v_____do__lift_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2290_, lean_object* v_methods_2291_, lean_object* v_____do__lift_2292_, lean_object* v_____do__lift_2293_, lean_object* v_x_2294_, lean_object* v_toPure_2295_, lean_object* v_inst_2296_, lean_object* v___f_2297_, lean_object* v_toBind_2298_, lean_object* v_setNextMacroScope_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_toMonadRef_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_toMonadExceptOf_2306_, lean_object* v_getNextMacroScope_2307_, lean_object* v_____do__lift_2308_){
_start:
{
lean_object* v_getRecDepth_2309_; lean_object* v_getMaxRecDepth_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; 
v_getRecDepth_2309_ = lean_ctor_get(v_inst_2290_, 1);
lean_inc(v_getRecDepth_2309_);
v_getMaxRecDepth_2310_ = lean_ctor_get(v_inst_2290_, 2);
lean_inc(v_getMaxRecDepth_2310_);
lean_dec_ref(v_inst_2290_);
lean_inc(v_toBind_2298_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2311_, 0, v_methods_2291_);
lean_closure_set(v___f_2311_, 1, v_____do__lift_2308_);
lean_closure_set(v___f_2311_, 2, v_____do__lift_2292_);
lean_closure_set(v___f_2311_, 3, v_____do__lift_2293_);
lean_closure_set(v___f_2311_, 4, v_x_2294_);
lean_closure_set(v___f_2311_, 5, v_toPure_2295_);
lean_closure_set(v___f_2311_, 6, v_inst_2296_);
lean_closure_set(v___f_2311_, 7, v___f_2297_);
lean_closure_set(v___f_2311_, 8, v_toBind_2298_);
lean_closure_set(v___f_2311_, 9, v_setNextMacroScope_2299_);
lean_closure_set(v___f_2311_, 10, v_inst_2300_);
lean_closure_set(v___f_2311_, 11, v_inst_2301_);
lean_closure_set(v___f_2311_, 12, v_inst_2302_);
lean_closure_set(v___f_2311_, 13, v_toMonadRef_2303_);
lean_closure_set(v___f_2311_, 14, v_inst_2304_);
lean_closure_set(v___f_2311_, 15, v_inst_2305_);
lean_closure_set(v___f_2311_, 16, v_toMonadExceptOf_2306_);
lean_closure_set(v___f_2311_, 17, v_getNextMacroScope_2307_);
lean_closure_set(v___f_2311_, 18, v_getMaxRecDepth_2310_);
v___x_2312_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v_getRecDepth_2309_, v___f_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2313_ = _args[0];
lean_object* v_methods_2314_ = _args[1];
lean_object* v_____do__lift_2315_ = _args[2];
lean_object* v_____do__lift_2316_ = _args[3];
lean_object* v_x_2317_ = _args[4];
lean_object* v_toPure_2318_ = _args[5];
lean_object* v_inst_2319_ = _args[6];
lean_object* v___f_2320_ = _args[7];
lean_object* v_toBind_2321_ = _args[8];
lean_object* v_setNextMacroScope_2322_ = _args[9];
lean_object* v_inst_2323_ = _args[10];
lean_object* v_inst_2324_ = _args[11];
lean_object* v_inst_2325_ = _args[12];
lean_object* v_toMonadRef_2326_ = _args[13];
lean_object* v_inst_2327_ = _args[14];
lean_object* v_inst_2328_ = _args[15];
lean_object* v_toMonadExceptOf_2329_ = _args[16];
lean_object* v_getNextMacroScope_2330_ = _args[17];
lean_object* v_____do__lift_2331_ = _args[18];
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2313_, v_methods_2314_, v_____do__lift_2315_, v_____do__lift_2316_, v_x_2317_, v_toPure_2318_, v_inst_2319_, v___f_2320_, v_toBind_2321_, v_setNextMacroScope_2322_, v_inst_2323_, v_inst_2324_, v_inst_2325_, v_toMonadRef_2326_, v_inst_2327_, v_inst_2328_, v_toMonadExceptOf_2329_, v_getNextMacroScope_2330_, v_____do__lift_2331_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2333_, lean_object* v_methods_2334_, lean_object* v_____do__lift_2335_, lean_object* v_x_2336_, lean_object* v_toPure_2337_, lean_object* v_inst_2338_, lean_object* v___f_2339_, lean_object* v_toBind_2340_, lean_object* v_setNextMacroScope_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_toMonadRef_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_toMonadExceptOf_2348_, lean_object* v_getNextMacroScope_2349_, lean_object* v_getContext_2350_, lean_object* v_____do__lift_2351_){
_start:
{
lean_object* v___f_2352_; lean_object* v___x_2353_; 
lean_inc(v_toBind_2340_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2352_, 0, v_inst_2333_);
lean_closure_set(v___f_2352_, 1, v_methods_2334_);
lean_closure_set(v___f_2352_, 2, v_____do__lift_2351_);
lean_closure_set(v___f_2352_, 3, v_____do__lift_2335_);
lean_closure_set(v___f_2352_, 4, v_x_2336_);
lean_closure_set(v___f_2352_, 5, v_toPure_2337_);
lean_closure_set(v___f_2352_, 6, v_inst_2338_);
lean_closure_set(v___f_2352_, 7, v___f_2339_);
lean_closure_set(v___f_2352_, 8, v_toBind_2340_);
lean_closure_set(v___f_2352_, 9, v_setNextMacroScope_2341_);
lean_closure_set(v___f_2352_, 10, v_inst_2342_);
lean_closure_set(v___f_2352_, 11, v_inst_2343_);
lean_closure_set(v___f_2352_, 12, v_inst_2344_);
lean_closure_set(v___f_2352_, 13, v_toMonadRef_2345_);
lean_closure_set(v___f_2352_, 14, v_inst_2346_);
lean_closure_set(v___f_2352_, 15, v_inst_2347_);
lean_closure_set(v___f_2352_, 16, v_toMonadExceptOf_2348_);
lean_closure_set(v___f_2352_, 17, v_getNextMacroScope_2349_);
v___x_2353_ = lean_apply_4(v_toBind_2340_, lean_box(0), lean_box(0), v_getContext_2350_, v___f_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2354_ = _args[0];
lean_object* v_methods_2355_ = _args[1];
lean_object* v_____do__lift_2356_ = _args[2];
lean_object* v_x_2357_ = _args[3];
lean_object* v_toPure_2358_ = _args[4];
lean_object* v_inst_2359_ = _args[5];
lean_object* v___f_2360_ = _args[6];
lean_object* v_toBind_2361_ = _args[7];
lean_object* v_setNextMacroScope_2362_ = _args[8];
lean_object* v_inst_2363_ = _args[9];
lean_object* v_inst_2364_ = _args[10];
lean_object* v_inst_2365_ = _args[11];
lean_object* v_toMonadRef_2366_ = _args[12];
lean_object* v_inst_2367_ = _args[13];
lean_object* v_inst_2368_ = _args[14];
lean_object* v_toMonadExceptOf_2369_ = _args[15];
lean_object* v_getNextMacroScope_2370_ = _args[16];
lean_object* v_getContext_2371_ = _args[17];
lean_object* v_____do__lift_2372_ = _args[18];
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2354_, v_methods_2355_, v_____do__lift_2356_, v_x_2357_, v_toPure_2358_, v_inst_2359_, v___f_2360_, v_toBind_2361_, v_setNextMacroScope_2362_, v_inst_2363_, v_inst_2364_, v_inst_2365_, v_toMonadRef_2366_, v_inst_2367_, v_inst_2368_, v_toMonadExceptOf_2369_, v_getNextMacroScope_2370_, v_getContext_2371_, v_____do__lift_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2374_, lean_object* v_inst_2375_, lean_object* v_methods_2376_, lean_object* v_x_2377_, lean_object* v_toPure_2378_, lean_object* v_inst_2379_, lean_object* v___f_2380_, lean_object* v_toBind_2381_, lean_object* v_setNextMacroScope_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_toMonadRef_2386_, lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_toMonadExceptOf_2389_, lean_object* v_getNextMacroScope_2390_, lean_object* v_____do__lift_2391_){
_start:
{
lean_object* v_getCurrMacroScope_2392_; lean_object* v_getContext_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; 
v_getCurrMacroScope_2392_ = lean_ctor_get(v_toMonadQuotation_2374_, 1);
lean_inc(v_getCurrMacroScope_2392_);
v_getContext_2393_ = lean_ctor_get(v_toMonadQuotation_2374_, 2);
lean_inc(v_getContext_2393_);
lean_dec_ref(v_toMonadQuotation_2374_);
lean_inc(v_toBind_2381_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2394_, 0, v_inst_2375_);
lean_closure_set(v___f_2394_, 1, v_methods_2376_);
lean_closure_set(v___f_2394_, 2, v_____do__lift_2391_);
lean_closure_set(v___f_2394_, 3, v_x_2377_);
lean_closure_set(v___f_2394_, 4, v_toPure_2378_);
lean_closure_set(v___f_2394_, 5, v_inst_2379_);
lean_closure_set(v___f_2394_, 6, v___f_2380_);
lean_closure_set(v___f_2394_, 7, v_toBind_2381_);
lean_closure_set(v___f_2394_, 8, v_setNextMacroScope_2382_);
lean_closure_set(v___f_2394_, 9, v_inst_2383_);
lean_closure_set(v___f_2394_, 10, v_inst_2384_);
lean_closure_set(v___f_2394_, 11, v_inst_2385_);
lean_closure_set(v___f_2394_, 12, v_toMonadRef_2386_);
lean_closure_set(v___f_2394_, 13, v_inst_2387_);
lean_closure_set(v___f_2394_, 14, v_inst_2388_);
lean_closure_set(v___f_2394_, 15, v_toMonadExceptOf_2389_);
lean_closure_set(v___f_2394_, 16, v_getNextMacroScope_2390_);
lean_closure_set(v___f_2394_, 17, v_getContext_2393_);
v___x_2395_ = lean_apply_4(v_toBind_2381_, lean_box(0), lean_box(0), v_getCurrMacroScope_2392_, v___f_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2396_ = _args[0];
lean_object* v_inst_2397_ = _args[1];
lean_object* v_methods_2398_ = _args[2];
lean_object* v_x_2399_ = _args[3];
lean_object* v_toPure_2400_ = _args[4];
lean_object* v_inst_2401_ = _args[5];
lean_object* v___f_2402_ = _args[6];
lean_object* v_toBind_2403_ = _args[7];
lean_object* v_setNextMacroScope_2404_ = _args[8];
lean_object* v_inst_2405_ = _args[9];
lean_object* v_inst_2406_ = _args[10];
lean_object* v_inst_2407_ = _args[11];
lean_object* v_toMonadRef_2408_ = _args[12];
lean_object* v_inst_2409_ = _args[13];
lean_object* v_inst_2410_ = _args[14];
lean_object* v_toMonadExceptOf_2411_ = _args[15];
lean_object* v_getNextMacroScope_2412_ = _args[16];
lean_object* v_____do__lift_2413_ = _args[17];
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2396_, v_inst_2397_, v_methods_2398_, v_x_2399_, v_toPure_2400_, v_inst_2401_, v___f_2402_, v_toBind_2403_, v_setNextMacroScope_2404_, v_inst_2405_, v_inst_2406_, v_inst_2407_, v_toMonadRef_2408_, v_inst_2409_, v_inst_2410_, v_toMonadExceptOf_2411_, v_getNextMacroScope_2412_, v_____do__lift_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2415_, lean_object* v_env_2416_, lean_object* v_currNamespace_2417_, lean_object* v_opts_2418_, lean_object* v___x_2419_, lean_object* v___f_2420_, lean_object* v___f_2421_, lean_object* v_toMonadQuotation_2422_, lean_object* v_inst_2423_, lean_object* v_x_2424_, lean_object* v_toPure_2425_, lean_object* v_inst_2426_, lean_object* v___f_2427_, lean_object* v_toBind_2428_, lean_object* v_setNextMacroScope_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_toMonadExceptOf_2435_, lean_object* v_getNextMacroScope_2436_, lean_object* v_openDecls_2437_){
_start:
{
lean_object* v_getRef_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v_methods_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; 
v_getRef_2438_ = lean_ctor_get(v_toMonadRef_2415_, 0);
lean_inc(v_getRef_2438_);
lean_inc(v_openDecls_2437_);
lean_inc_n(v_currNamespace_2417_, 2);
lean_inc_ref(v_env_2416_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2439_, 0, v_env_2416_);
lean_closure_set(v___f_2439_, 1, v_currNamespace_2417_);
lean_closure_set(v___f_2439_, 2, v_openDecls_2437_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2440_, 0, v_env_2416_);
lean_closure_set(v___f_2440_, 1, v_opts_2418_);
lean_closure_set(v___f_2440_, 2, v_currNamespace_2417_);
lean_closure_set(v___f_2440_, 3, v_openDecls_2437_);
v___x_2441_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2441_, 0, lean_box(0));
lean_closure_set(v___x_2441_, 1, lean_box(0));
lean_closure_set(v___x_2441_, 2, v___x_2419_);
lean_closure_set(v___x_2441_, 3, lean_box(0));
lean_closure_set(v___x_2441_, 4, v_currNamespace_2417_);
v_methods_2442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2442_, 0, v___f_2420_);
lean_ctor_set(v_methods_2442_, 1, v___x_2441_);
lean_ctor_set(v_methods_2442_, 2, v___f_2421_);
lean_ctor_set(v_methods_2442_, 3, v___f_2439_);
lean_ctor_set(v_methods_2442_, 4, v___f_2440_);
lean_inc(v_toBind_2428_);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2443_, 0, v_toMonadQuotation_2422_);
lean_closure_set(v___f_2443_, 1, v_inst_2423_);
lean_closure_set(v___f_2443_, 2, v_methods_2442_);
lean_closure_set(v___f_2443_, 3, v_x_2424_);
lean_closure_set(v___f_2443_, 4, v_toPure_2425_);
lean_closure_set(v___f_2443_, 5, v_inst_2426_);
lean_closure_set(v___f_2443_, 6, v___f_2427_);
lean_closure_set(v___f_2443_, 7, v_toBind_2428_);
lean_closure_set(v___f_2443_, 8, v_setNextMacroScope_2429_);
lean_closure_set(v___f_2443_, 9, v_inst_2430_);
lean_closure_set(v___f_2443_, 10, v_inst_2431_);
lean_closure_set(v___f_2443_, 11, v_inst_2432_);
lean_closure_set(v___f_2443_, 12, v_toMonadRef_2415_);
lean_closure_set(v___f_2443_, 13, v_inst_2433_);
lean_closure_set(v___f_2443_, 14, v_inst_2434_);
lean_closure_set(v___f_2443_, 15, v_toMonadExceptOf_2435_);
lean_closure_set(v___f_2443_, 16, v_getNextMacroScope_2436_);
v___x_2444_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v_getRef_2438_, v___f_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2445_ = _args[0];
lean_object* v_env_2446_ = _args[1];
lean_object* v_currNamespace_2447_ = _args[2];
lean_object* v_opts_2448_ = _args[3];
lean_object* v___x_2449_ = _args[4];
lean_object* v___f_2450_ = _args[5];
lean_object* v___f_2451_ = _args[6];
lean_object* v_toMonadQuotation_2452_ = _args[7];
lean_object* v_inst_2453_ = _args[8];
lean_object* v_x_2454_ = _args[9];
lean_object* v_toPure_2455_ = _args[10];
lean_object* v_inst_2456_ = _args[11];
lean_object* v___f_2457_ = _args[12];
lean_object* v_toBind_2458_ = _args[13];
lean_object* v_setNextMacroScope_2459_ = _args[14];
lean_object* v_inst_2460_ = _args[15];
lean_object* v_inst_2461_ = _args[16];
lean_object* v_inst_2462_ = _args[17];
lean_object* v_inst_2463_ = _args[18];
lean_object* v_inst_2464_ = _args[19];
lean_object* v_toMonadExceptOf_2465_ = _args[20];
lean_object* v_getNextMacroScope_2466_ = _args[21];
lean_object* v_openDecls_2467_ = _args[22];
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2445_, v_env_2446_, v_currNamespace_2447_, v_opts_2448_, v___x_2449_, v___f_2450_, v___f_2451_, v_toMonadQuotation_2452_, v_inst_2453_, v_x_2454_, v_toPure_2455_, v_inst_2456_, v___f_2457_, v_toBind_2458_, v_setNextMacroScope_2459_, v_inst_2460_, v_inst_2461_, v_inst_2462_, v_inst_2463_, v_inst_2464_, v_toMonadExceptOf_2465_, v_getNextMacroScope_2466_, v_openDecls_2467_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2469_, lean_object* v_env_2470_, lean_object* v_opts_2471_, lean_object* v___x_2472_, lean_object* v___f_2473_, lean_object* v___f_2474_, lean_object* v_toMonadQuotation_2475_, lean_object* v_inst_2476_, lean_object* v_x_2477_, lean_object* v_toPure_2478_, lean_object* v_inst_2479_, lean_object* v___f_2480_, lean_object* v_toBind_2481_, lean_object* v_setNextMacroScope_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_toMonadExceptOf_2488_, lean_object* v_getNextMacroScope_2489_, lean_object* v_getOpenDecls_2490_, lean_object* v_currNamespace_2491_){
_start:
{
lean_object* v___f_2492_; lean_object* v___x_2493_; 
lean_inc(v_toBind_2481_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2492_, 0, v_toMonadRef_2469_);
lean_closure_set(v___f_2492_, 1, v_env_2470_);
lean_closure_set(v___f_2492_, 2, v_currNamespace_2491_);
lean_closure_set(v___f_2492_, 3, v_opts_2471_);
lean_closure_set(v___f_2492_, 4, v___x_2472_);
lean_closure_set(v___f_2492_, 5, v___f_2473_);
lean_closure_set(v___f_2492_, 6, v___f_2474_);
lean_closure_set(v___f_2492_, 7, v_toMonadQuotation_2475_);
lean_closure_set(v___f_2492_, 8, v_inst_2476_);
lean_closure_set(v___f_2492_, 9, v_x_2477_);
lean_closure_set(v___f_2492_, 10, v_toPure_2478_);
lean_closure_set(v___f_2492_, 11, v_inst_2479_);
lean_closure_set(v___f_2492_, 12, v___f_2480_);
lean_closure_set(v___f_2492_, 13, v_toBind_2481_);
lean_closure_set(v___f_2492_, 14, v_setNextMacroScope_2482_);
lean_closure_set(v___f_2492_, 15, v_inst_2483_);
lean_closure_set(v___f_2492_, 16, v_inst_2484_);
lean_closure_set(v___f_2492_, 17, v_inst_2485_);
lean_closure_set(v___f_2492_, 18, v_inst_2486_);
lean_closure_set(v___f_2492_, 19, v_inst_2487_);
lean_closure_set(v___f_2492_, 20, v_toMonadExceptOf_2488_);
lean_closure_set(v___f_2492_, 21, v_getNextMacroScope_2489_);
v___x_2493_ = lean_apply_4(v_toBind_2481_, lean_box(0), lean_box(0), v_getOpenDecls_2490_, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2494_ = _args[0];
lean_object* v_env_2495_ = _args[1];
lean_object* v_opts_2496_ = _args[2];
lean_object* v___x_2497_ = _args[3];
lean_object* v___f_2498_ = _args[4];
lean_object* v___f_2499_ = _args[5];
lean_object* v_toMonadQuotation_2500_ = _args[6];
lean_object* v_inst_2501_ = _args[7];
lean_object* v_x_2502_ = _args[8];
lean_object* v_toPure_2503_ = _args[9];
lean_object* v_inst_2504_ = _args[10];
lean_object* v___f_2505_ = _args[11];
lean_object* v_toBind_2506_ = _args[12];
lean_object* v_setNextMacroScope_2507_ = _args[13];
lean_object* v_inst_2508_ = _args[14];
lean_object* v_inst_2509_ = _args[15];
lean_object* v_inst_2510_ = _args[16];
lean_object* v_inst_2511_ = _args[17];
lean_object* v_inst_2512_ = _args[18];
lean_object* v_toMonadExceptOf_2513_ = _args[19];
lean_object* v_getNextMacroScope_2514_ = _args[20];
lean_object* v_getOpenDecls_2515_ = _args[21];
lean_object* v_currNamespace_2516_ = _args[22];
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2494_, v_env_2495_, v_opts_2496_, v___x_2497_, v___f_2498_, v___f_2499_, v_toMonadQuotation_2500_, v_inst_2501_, v_x_2502_, v_toPure_2503_, v_inst_2504_, v___f_2505_, v_toBind_2506_, v_setNextMacroScope_2507_, v_inst_2508_, v_inst_2509_, v_inst_2510_, v_inst_2511_, v_inst_2512_, v_toMonadExceptOf_2513_, v_getNextMacroScope_2514_, v_getOpenDecls_2515_, v_currNamespace_2516_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2518_, lean_object* v_toMonadRef_2519_, lean_object* v_env_2520_, lean_object* v___x_2521_, lean_object* v___f_2522_, lean_object* v___f_2523_, lean_object* v_toMonadQuotation_2524_, lean_object* v_inst_2525_, lean_object* v_x_2526_, lean_object* v_toPure_2527_, lean_object* v_inst_2528_, lean_object* v___f_2529_, lean_object* v_toBind_2530_, lean_object* v_setNextMacroScope_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_toMonadExceptOf_2537_, lean_object* v_getNextMacroScope_2538_, lean_object* v_opts_2539_){
_start:
{
lean_object* v_getCurrNamespace_2540_; lean_object* v_getOpenDecls_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; 
v_getCurrNamespace_2540_ = lean_ctor_get(v_inst_2518_, 0);
lean_inc(v_getCurrNamespace_2540_);
v_getOpenDecls_2541_ = lean_ctor_get(v_inst_2518_, 1);
lean_inc(v_getOpenDecls_2541_);
lean_dec_ref(v_inst_2518_);
lean_inc(v_toBind_2530_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2542_, 0, v_toMonadRef_2519_);
lean_closure_set(v___f_2542_, 1, v_env_2520_);
lean_closure_set(v___f_2542_, 2, v_opts_2539_);
lean_closure_set(v___f_2542_, 3, v___x_2521_);
lean_closure_set(v___f_2542_, 4, v___f_2522_);
lean_closure_set(v___f_2542_, 5, v___f_2523_);
lean_closure_set(v___f_2542_, 6, v_toMonadQuotation_2524_);
lean_closure_set(v___f_2542_, 7, v_inst_2525_);
lean_closure_set(v___f_2542_, 8, v_x_2526_);
lean_closure_set(v___f_2542_, 9, v_toPure_2527_);
lean_closure_set(v___f_2542_, 10, v_inst_2528_);
lean_closure_set(v___f_2542_, 11, v___f_2529_);
lean_closure_set(v___f_2542_, 12, v_toBind_2530_);
lean_closure_set(v___f_2542_, 13, v_setNextMacroScope_2531_);
lean_closure_set(v___f_2542_, 14, v_inst_2532_);
lean_closure_set(v___f_2542_, 15, v_inst_2533_);
lean_closure_set(v___f_2542_, 16, v_inst_2534_);
lean_closure_set(v___f_2542_, 17, v_inst_2535_);
lean_closure_set(v___f_2542_, 18, v_inst_2536_);
lean_closure_set(v___f_2542_, 19, v_toMonadExceptOf_2537_);
lean_closure_set(v___f_2542_, 20, v_getNextMacroScope_2538_);
lean_closure_set(v___f_2542_, 21, v_getOpenDecls_2541_);
v___x_2543_ = lean_apply_4(v_toBind_2530_, lean_box(0), lean_box(0), v_getCurrNamespace_2540_, v___f_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2544_ = _args[0];
lean_object* v_toMonadRef_2545_ = _args[1];
lean_object* v_env_2546_ = _args[2];
lean_object* v___x_2547_ = _args[3];
lean_object* v___f_2548_ = _args[4];
lean_object* v___f_2549_ = _args[5];
lean_object* v_toMonadQuotation_2550_ = _args[6];
lean_object* v_inst_2551_ = _args[7];
lean_object* v_x_2552_ = _args[8];
lean_object* v_toPure_2553_ = _args[9];
lean_object* v_inst_2554_ = _args[10];
lean_object* v___f_2555_ = _args[11];
lean_object* v_toBind_2556_ = _args[12];
lean_object* v_setNextMacroScope_2557_ = _args[13];
lean_object* v_inst_2558_ = _args[14];
lean_object* v_inst_2559_ = _args[15];
lean_object* v_inst_2560_ = _args[16];
lean_object* v_inst_2561_ = _args[17];
lean_object* v_inst_2562_ = _args[18];
lean_object* v_toMonadExceptOf_2563_ = _args[19];
lean_object* v_getNextMacroScope_2564_ = _args[20];
lean_object* v_opts_2565_ = _args[21];
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2544_, v_toMonadRef_2545_, v_env_2546_, v___x_2547_, v___f_2548_, v___f_2549_, v_toMonadQuotation_2550_, v_inst_2551_, v_x_2552_, v_toPure_2553_, v_inst_2554_, v___f_2555_, v_toBind_2556_, v_setNextMacroScope_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_inst_2562_, v_toMonadExceptOf_2563_, v_getNextMacroScope_2564_, v_opts_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v___x_2567_, lean_object* v___x_2568_, lean_object* v_inst_2569_, lean_object* v_toMonadRef_2570_, lean_object* v___x_2571_, lean_object* v_toMonadQuotation_2572_, lean_object* v_inst_2573_, lean_object* v_x_2574_, lean_object* v_toPure_2575_, lean_object* v_inst_2576_, lean_object* v___f_2577_, lean_object* v_toBind_2578_, lean_object* v_setNextMacroScope_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_toMonadExceptOf_2585_, lean_object* v_getNextMacroScope_2586_, lean_object* v_env_2587_){
_start:
{
lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; 
lean_inc_ref_n(v_env_2587_, 2);
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2588_, 0, v_env_2587_);
lean_closure_set(v___f_2588_, 1, v___x_2567_);
lean_closure_set(v___f_2588_, 2, v___x_2568_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2589_, 0, v_env_2587_);
lean_inc(v_inst_2582_);
lean_inc(v_toBind_2578_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2590_, 0, v_inst_2569_);
lean_closure_set(v___f_2590_, 1, v_toMonadRef_2570_);
lean_closure_set(v___f_2590_, 2, v_env_2587_);
lean_closure_set(v___f_2590_, 3, v___x_2571_);
lean_closure_set(v___f_2590_, 4, v___f_2588_);
lean_closure_set(v___f_2590_, 5, v___f_2589_);
lean_closure_set(v___f_2590_, 6, v_toMonadQuotation_2572_);
lean_closure_set(v___f_2590_, 7, v_inst_2573_);
lean_closure_set(v___f_2590_, 8, v_x_2574_);
lean_closure_set(v___f_2590_, 9, v_toPure_2575_);
lean_closure_set(v___f_2590_, 10, v_inst_2576_);
lean_closure_set(v___f_2590_, 11, v___f_2577_);
lean_closure_set(v___f_2590_, 12, v_toBind_2578_);
lean_closure_set(v___f_2590_, 13, v_setNextMacroScope_2579_);
lean_closure_set(v___f_2590_, 14, v_inst_2580_);
lean_closure_set(v___f_2590_, 15, v_inst_2581_);
lean_closure_set(v___f_2590_, 16, v_inst_2582_);
lean_closure_set(v___f_2590_, 17, v_inst_2583_);
lean_closure_set(v___f_2590_, 18, v_inst_2584_);
lean_closure_set(v___f_2590_, 19, v_toMonadExceptOf_2585_);
lean_closure_set(v___f_2590_, 20, v_getNextMacroScope_2586_);
v___x_2591_ = lean_apply_4(v_toBind_2578_, lean_box(0), lean_box(0), v_inst_2582_, v___f_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_2592_ = _args[0];
lean_object* v___x_2593_ = _args[1];
lean_object* v_inst_2594_ = _args[2];
lean_object* v_toMonadRef_2595_ = _args[3];
lean_object* v___x_2596_ = _args[4];
lean_object* v_toMonadQuotation_2597_ = _args[5];
lean_object* v_inst_2598_ = _args[6];
lean_object* v_x_2599_ = _args[7];
lean_object* v_toPure_2600_ = _args[8];
lean_object* v_inst_2601_ = _args[9];
lean_object* v___f_2602_ = _args[10];
lean_object* v_toBind_2603_ = _args[11];
lean_object* v_setNextMacroScope_2604_ = _args[12];
lean_object* v_inst_2605_ = _args[13];
lean_object* v_inst_2606_ = _args[14];
lean_object* v_inst_2607_ = _args[15];
lean_object* v_inst_2608_ = _args[16];
lean_object* v_inst_2609_ = _args[17];
lean_object* v_toMonadExceptOf_2610_ = _args[18];
lean_object* v_getNextMacroScope_2611_ = _args[19];
lean_object* v_env_2612_ = _args[20];
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v___x_2592_, v___x_2593_, v_inst_2594_, v_toMonadRef_2595_, v___x_2596_, v_toMonadQuotation_2597_, v_inst_2598_, v_x_2599_, v_toPure_2600_, v_inst_2601_, v___f_2602_, v_toBind_2603_, v_setNextMacroScope_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v_inst_2609_, v_toMonadExceptOf_2610_, v_getNextMacroScope_2611_, v_env_2612_);
return v_res_2613_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_EStateM_nonBacktrackable(lean_box(0));
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2635_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___f_2637_; 
v___x_2636_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2637_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2637_, 0, v___x_2636_);
return v___f_2637_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___f_2639_; 
v___x_2638_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2639_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2639_, 0, v___x_2638_);
return v___f_2639_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; 
v___f_2640_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2641_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___f_2641_);
lean_ctor_set(v___x_2642_, 1, v___f_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_x_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v_toApplicative_2657_; lean_object* v_toBind_2658_; lean_object* v_getEnv_2659_; lean_object* v_toMonadExceptOf_2660_; lean_object* v_toMonadRef_2661_; lean_object* v_toMonadQuotation_2662_; lean_object* v_getNextMacroScope_2663_; lean_object* v_setNextMacroScope_2664_; lean_object* v_toPure_2665_; lean_object* v___x_2666_; lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; 
v___x_2655_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2656_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2657_ = lean_ctor_get(v_inst_2645_, 0);
v_toBind_2658_ = lean_ctor_get(v_inst_2645_, 1);
lean_inc_n(v_toBind_2658_, 3);
v_getEnv_2659_ = lean_ctor_get(v_inst_2647_, 0);
lean_inc(v_getEnv_2659_);
v_toMonadExceptOf_2660_ = lean_ctor_get(v_inst_2649_, 0);
lean_inc_ref(v_toMonadExceptOf_2660_);
v_toMonadRef_2661_ = lean_ctor_get(v_inst_2649_, 1);
lean_inc_ref_n(v_toMonadRef_2661_, 2);
v_toMonadQuotation_2662_ = lean_ctor_get(v_inst_2646_, 0);
lean_inc_ref(v_toMonadQuotation_2662_);
v_getNextMacroScope_2663_ = lean_ctor_get(v_inst_2646_, 1);
lean_inc(v_getNextMacroScope_2663_);
v_setNextMacroScope_2664_ = lean_ctor_get(v_inst_2646_, 2);
lean_inc(v_setNextMacroScope_2664_);
lean_dec_ref(v_inst_2646_);
v_toPure_2665_ = lean_ctor_get(v_toApplicative_2657_, 1);
lean_inc_n(v_toPure_2665_, 2);
v___x_2666_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2652_);
lean_inc(v_inst_2653_);
lean_inc_ref(v_inst_2645_);
lean_inc_ref(v_inst_2651_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2667_, 0, v_inst_2651_);
lean_closure_set(v___f_2667_, 1, v_toPure_2665_);
lean_closure_set(v___f_2667_, 2, v_inst_2645_);
lean_closure_set(v___f_2667_, 3, v_toMonadRef_2661_);
lean_closure_set(v___f_2667_, 4, v_inst_2653_);
lean_closure_set(v___f_2667_, 5, v_toBind_2658_);
lean_closure_set(v___f_2667_, 6, v_inst_2652_);
v___f_2668_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2668_, 0, v___x_2656_);
lean_closure_set(v___f_2668_, 1, v___x_2666_);
lean_closure_set(v___f_2668_, 2, v_inst_2650_);
lean_closure_set(v___f_2668_, 3, v_toMonadRef_2661_);
lean_closure_set(v___f_2668_, 4, v___x_2655_);
lean_closure_set(v___f_2668_, 5, v_toMonadQuotation_2662_);
lean_closure_set(v___f_2668_, 6, v_inst_2648_);
lean_closure_set(v___f_2668_, 7, v_x_2654_);
lean_closure_set(v___f_2668_, 8, v_toPure_2665_);
lean_closure_set(v___f_2668_, 9, v_inst_2645_);
lean_closure_set(v___f_2668_, 10, v___f_2667_);
lean_closure_set(v___f_2668_, 11, v_toBind_2658_);
lean_closure_set(v___f_2668_, 12, v_setNextMacroScope_2664_);
lean_closure_set(v___f_2668_, 13, v_inst_2647_);
lean_closure_set(v___f_2668_, 14, v_inst_2651_);
lean_closure_set(v___f_2668_, 15, v_inst_2652_);
lean_closure_set(v___f_2668_, 16, v_inst_2653_);
lean_closure_set(v___f_2668_, 17, v_inst_2649_);
lean_closure_set(v___f_2668_, 18, v_toMonadExceptOf_2660_);
lean_closure_set(v___f_2668_, 19, v_getNextMacroScope_2663_);
v___x_2669_ = lean_apply_4(v_toBind_2658_, lean_box(0), lean_box(0), v_getEnv_2659_, v___f_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2670_, lean_object* v_00_u03b1_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_x_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2672_, v_inst_2673_, v_inst_2674_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2684_, lean_object* v_00_u03b1_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Elab_liftMacroM(v_m_2684_, v_00_u03b1_2685_, v_inst_2686_, v_inst_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_x_2696_);
lean_dec(v_inst_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_x_2707_, lean_object* v_stx_2708_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_apply_1(v_x_2707_, v_stx_2708_);
v___x_2710_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_x_2722_, lean_object* v_stx_2723_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_apply_1(v_x_2722_, v_stx_2723_);
v___x_2725_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_inst_2715_, v_inst_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_x_2737_, lean_object* v_stx_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Elab_adaptMacro(v_m_2726_, v_inst_2727_, v_inst_2728_, v_inst_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v_inst_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_x_2737_, v_stx_2738_);
lean_dec(v_inst_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2740_, lean_object* v_currNamespace_2741_, lean_object* v_idx_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_name_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_inc(v_idx_2742_);
lean_inc(v_baseName_2740_);
v_name_2745_ = lean_name_append_index_after(v_baseName_2740_, v_idx_2742_);
lean_inc(v_name_2745_);
lean_inc(v_currNamespace_2741_);
v___x_2746_ = l_Lean_Name_append(v_currNamespace_2741_, v_name_2745_);
v___x_2747_ = l_Lean_Macro_hasDecl(v___x_2746_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; uint8_t v___x_2749_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
v___x_2749_ = lean_unbox(v_a_2748_);
lean_dec(v_a_2748_);
if (v___x_2749_ == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_idx_2742_);
lean_dec(v_currNamespace_2741_);
lean_dec(v_baseName_2740_);
v_a_2750_ = lean_ctor_get(v___x_2747_, 1);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; 
v_unused_2758_ = lean_ctor_get(v___x_2747_, 0);
lean_dec(v_unused_2758_);
v___x_2752_ = v___x_2747_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2747_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_name_2745_);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_name_2745_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec(v_name_2745_);
v_a_2759_ = lean_ctor_get(v___x_2747_, 1);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2747_);
v___x_2760_ = lean_unsigned_to_nat(1u);
v___x_2761_ = lean_nat_add(v_idx_2742_, v___x_2760_);
lean_dec(v_idx_2742_);
v_idx_2742_ = v___x_2761_;
v_a_2744_ = v_a_2759_;
goto _start;
}
}
else
{
lean_object* v_a_2763_; lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_name_2745_);
lean_dec(v_idx_2742_);
lean_dec(v_currNamespace_2741_);
lean_dec(v_baseName_2740_);
v_a_2763_ = lean_ctor_get(v___x_2747_, 0);
v_a_2764_ = lean_ctor_get(v___x_2747_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2747_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_inc(v_a_2763_);
lean_dec(v___x_2747_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2763_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2772_, lean_object* v_currNamespace_2773_, lean_object* v_idx_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2772_, v_currNamespace_2773_, v_idx_2774_, v_a_2775_, v_a_2776_);
lean_dec_ref(v_a_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Macro_getCurrNamespace(v_a_2779_, v_a_2780_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_n(v_a_2782_, 2);
v_a_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2781_);
lean_inc(v_baseName_2778_);
v___x_2784_ = l_Lean_Name_append(v_a_2782_, v_baseName_2778_);
v___x_2785_ = l_Lean_Macro_hasDecl(v___x_2784_, v_a_2779_, v_a_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; uint8_t v___x_2787_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
v___x_2787_ = lean_unbox(v_a_2786_);
lean_dec(v_a_2786_);
if (v___x_2787_ == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2782_);
v_a_2788_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2785_, 0);
lean_dec(v_unused_2796_);
v___x_2790_ = v___x_2785_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2785_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_baseName_2778_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_baseName_2778_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2785_, 1);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2785_);
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2778_, v_a_2782_, v___x_2798_, v_a_2779_, v_a_2797_);
return v___x_2799_;
}
}
else
{
lean_object* v_a_2800_; lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2782_);
lean_dec(v_baseName_2778_);
v_a_2800_ = lean_ctor_get(v___x_2785_, 0);
v_a_2801_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2785_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_inc(v_a_2800_);
lean_dec(v___x_2785_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2800_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_dec(v_baseName_2778_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2809_, v_a_2810_, v_a_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2812_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_name_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2821_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2822_ = l_Lean_MessageData_ofName(v_name_2820_);
v___x_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2821_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = l_Lean_logError___redArg(v_inst_2816_, v_inst_2817_, v_inst_2818_, v_inst_2819_, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_ex_2830_){
_start:
{
if (lean_obj_tag(v_ex_2830_) == 0)
{
lean_object* v_ref_2831_; lean_object* v_msg_2832_; lean_object* v___x_2833_; 
lean_dec(v_inst_2829_);
v_ref_2831_ = lean_ctor_get(v_ex_2830_, 0);
lean_inc(v_ref_2831_);
v_msg_2832_ = lean_ctor_get(v_ex_2830_, 1);
lean_inc_ref(v_msg_2832_);
lean_dec_ref(v_ex_2830_);
v___x_2833_ = l_Lean_logErrorAt___redArg(v_inst_2825_, v_inst_2826_, v_inst_2827_, v_inst_2828_, v_ref_2831_, v_msg_2832_);
return v___x_2833_;
}
else
{
lean_object* v_id_2834_; lean_object* v___f_2835_; uint8_t v___y_2837_; uint8_t v___x_2846_; 
v_id_2834_ = lean_ctor_get(v_ex_2830_, 0);
lean_inc(v_id_2834_);
lean_inc_ref(v_inst_2825_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2835_, 0, v_inst_2825_);
lean_closure_set(v___f_2835_, 1, v_inst_2826_);
lean_closure_set(v___f_2835_, 2, v_inst_2827_);
lean_closure_set(v___f_2835_, 3, v_inst_2828_);
v___x_2846_ = l_Lean_Elab_isAbortExceptionId(v_id_2834_);
if (v___x_2846_ == 0)
{
uint8_t v___x_2847_; 
v___x_2847_ = l_Lean_Exception_isInterrupt(v_ex_2830_);
lean_dec_ref(v_ex_2830_);
v___y_2837_ = v___x_2847_;
goto v___jp_2836_;
}
else
{
lean_dec_ref(v_ex_2830_);
v___y_2837_ = v___x_2846_;
goto v___jp_2836_;
}
v___jp_2836_:
{
if (v___y_2837_ == 0)
{
lean_object* v_toBind_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_toBind_2838_ = lean_ctor_get(v_inst_2825_, 1);
lean_inc(v_toBind_2838_);
lean_dec_ref(v_inst_2825_);
v___x_2839_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2839_, 0, v_id_2834_);
v___x_2840_ = lean_apply_2(v_inst_2829_, lean_box(0), v___x_2839_);
v___x_2841_ = lean_apply_4(v_toBind_2838_, lean_box(0), lean_box(0), v___x_2840_, v___f_2835_);
return v___x_2841_;
}
else
{
lean_object* v_toApplicative_2842_; lean_object* v_toPure_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec_ref(v___f_2835_);
lean_dec(v_id_2834_);
lean_dec(v_inst_2829_);
v_toApplicative_2842_ = lean_ctor_get(v_inst_2825_, 0);
lean_inc_ref(v_toApplicative_2842_);
lean_dec_ref(v_inst_2825_);
v_toPure_2843_ = lean_ctor_get(v_toApplicative_2842_, 1);
lean_inc(v_toPure_2843_);
lean_dec_ref(v_toApplicative_2842_);
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_apply_2(v_toPure_2843_, lean_box(0), v___x_2844_);
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_, lean_object* v_ex_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Elab_logException___redArg(v_inst_2849_, v_inst_2850_, v_inst_2851_, v_inst_2852_, v_inst_2853_, v_ex_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_ex_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Elab_logException___redArg(v_inst_2856_, v_inst_2857_, v_inst_2858_, v_inst_2859_, v_inst_2860_, v_ex_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_x_2869_){
_start:
{
lean_object* v_tryCatch_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; 
v_tryCatch_2870_ = lean_ctor_get(v_inst_2865_, 1);
lean_inc(v_tryCatch_2870_);
lean_dec_ref(v_inst_2865_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2871_, 0, v_inst_2863_);
lean_closure_set(v___f_2871_, 1, v_inst_2864_);
lean_closure_set(v___f_2871_, 2, v_inst_2866_);
lean_closure_set(v___f_2871_, 3, v_inst_2867_);
lean_closure_set(v___f_2871_, 4, v_inst_2868_);
v___x_2872_ = lean_apply_3(v_tryCatch_2870_, lean_box(0), v_x_2869_, v___f_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_x_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Elab_withLogging___redArg(v_inst_2874_, v_inst_2875_, v_inst_2876_, v_inst_2877_, v_inst_2878_, v_inst_2879_, v_x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2884_ = l_Lean_stringToMessageData(v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2885_, lean_object* v_ex_2886_, lean_object* v_toPure_2887_, lean_object* v_____do__lift_2888_){
_start:
{
lean_object* v_exPosition_2889_; lean_object* v_line_2890_; lean_object* v_column_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2911_; 
v_exPosition_2889_ = l_Lean_FileMap_toPosition(v_____do__lift_2888_, v_val_2885_);
v_line_2890_ = lean_ctor_get(v_exPosition_2889_, 0);
v_column_2891_ = lean_ctor_get(v_exPosition_2889_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_exPosition_2889_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2893_ = v_exPosition_2889_;
v_isShared_2894_ = v_isSharedCheck_2911_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_column_2891_);
lean_inc(v_line_2890_);
lean_dec(v_exPosition_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2911_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2895_ = l_Nat_reprFast(v_line_2890_);
v___x_2896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
v___x_2897_ = l_Lean_MessageData_ofFormat(v___x_2896_);
v___x_2898_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 7);
lean_ctor_set(v___x_2893_, 1, v___x_2898_);
lean_ctor_set(v___x_2893_, 0, v___x_2897_);
v___x_2900_ = v___x_2893_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2901_ = l_Nat_reprFast(v_column_2891_);
v___x_2902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = l_Lean_MessageData_ofFormat(v___x_2902_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2900_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_Exception_toMessageData(v_ex_2886_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_apply_2(v_toPure_2887_, lean_box(0), v___x_2908_);
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2912_, lean_object* v_ex_2913_, lean_object* v_toPure_2914_, lean_object* v_____do__lift_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2912_, v_ex_2913_, v_toPure_2914_, v_____do__lift_2915_);
lean_dec(v_val_2912_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2917_, lean_object* v_toPure_2918_, lean_object* v_inst_2919_, lean_object* v_toBind_2920_, lean_object* v_pos_2921_){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = l_Lean_Exception_getRef(v_ex_2917_);
v___x_2923_ = 0;
v___x_2924_ = l_Lean_Syntax_getPos_x3f(v___x_2922_, v___x_2923_);
lean_dec(v___x_2922_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v_toBind_2920_);
lean_dec_ref(v_inst_2919_);
v___x_2925_ = l_Lean_Exception_toMessageData(v_ex_2917_);
v___x_2926_ = lean_apply_2(v_toPure_2918_, lean_box(0), v___x_2925_);
return v___x_2926_;
}
else
{
lean_object* v_val_2927_; uint8_t v___x_2928_; 
v_val_2927_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v___x_2924_);
v___x_2928_ = lean_nat_dec_eq(v_pos_2921_, v_val_2927_);
if (v___x_2928_ == 0)
{
lean_object* v_toMonadFileMap_2929_; lean_object* v___f_2930_; lean_object* v___x_2931_; 
v_toMonadFileMap_2929_ = lean_ctor_get(v_inst_2919_, 0);
lean_inc(v_toMonadFileMap_2929_);
lean_dec_ref(v_inst_2919_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2930_, 0, v_val_2927_);
lean_closure_set(v___f_2930_, 1, v_ex_2917_);
lean_closure_set(v___f_2930_, 2, v_toPure_2918_);
v___x_2931_ = lean_apply_4(v_toBind_2920_, lean_box(0), lean_box(0), v_toMonadFileMap_2929_, v___f_2930_);
return v___x_2931_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v_val_2927_);
lean_dec(v_toBind_2920_);
lean_dec_ref(v_inst_2919_);
v___x_2932_ = l_Lean_Exception_toMessageData(v_ex_2917_);
v___x_2933_ = lean_apply_2(v_toPure_2918_, lean_box(0), v___x_2932_);
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2934_, lean_object* v_toPure_2935_, lean_object* v_inst_2936_, lean_object* v_toBind_2937_, lean_object* v_pos_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2934_, v_toPure_2935_, v_inst_2936_, v_toBind_2937_, v_pos_2938_);
lean_dec(v_pos_2938_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_ex_2942_){
_start:
{
lean_object* v_toApplicative_2943_; lean_object* v_toBind_2944_; lean_object* v_toPure_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; lean_object* v___x_2948_; 
v_toApplicative_2943_ = lean_ctor_get(v_inst_2940_, 0);
v_toBind_2944_ = lean_ctor_get(v_inst_2940_, 1);
lean_inc_n(v_toBind_2944_, 2);
v_toPure_2945_ = lean_ctor_get(v_toApplicative_2943_, 1);
lean_inc(v_toPure_2945_);
lean_inc_ref(v_inst_2941_);
v___x_2946_ = l_Lean_getRefPos___redArg(v_inst_2940_, v_inst_2941_);
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2947_, 0, v_ex_2942_);
lean_closure_set(v___f_2947_, 1, v_toPure_2945_);
lean_closure_set(v___f_2947_, 2, v_inst_2941_);
lean_closure_set(v___f_2947_, 3, v_toBind_2944_);
v___x_2948_ = lean_apply_4(v_toBind_2944_, lean_box(0), lean_box(0), v___x_2946_, v___f_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_ex_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2950_, v_inst_2951_, v_ex_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_x_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2954_, v_inst_2955_, v_x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_____do__lift_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2965_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_msg_2961_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = l_Lean_toMessageList(v_____do__lift_2964_);
v___x_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = l_Lean_throwError___redArg(v_inst_2962_, v_inst_2963_, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_msg_2973_, lean_object* v_exs_2974_){
_start:
{
lean_object* v_toBind_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; size_t v_sz_2978_; size_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_toBind_2975_ = lean_ctor_get(v_inst_2971_, 1);
lean_inc(v_toBind_2975_);
lean_inc_ref_n(v_inst_2971_, 2);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2976_, 0, v_inst_2971_);
lean_closure_set(v___f_2976_, 1, v_inst_2972_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2977_, 0, v_msg_2973_);
lean_closure_set(v___f_2977_, 1, v_inst_2971_);
lean_closure_set(v___f_2977_, 2, v_inst_2970_);
v_sz_2978_ = lean_array_size(v_exs_2974_);
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2971_, v___f_2976_, v_sz_2978_, v___x_2979_, v_exs_2974_);
v___x_2981_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v___x_2980_, v___f_2977_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2982_, lean_object* v_00_u03b1_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_msg_2987_, lean_object* v_exs_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2984_, v_inst_2985_, v_inst_2986_, v_msg_2987_, v_exs_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3057_ = 0;
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3059_ = l_Lean_registerTraceClass(v___x_3056_, v___x_3057_, v___x_3058_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_dec_ref(v___x_3059_);
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3061_ = l_Lean_registerTraceClass(v___x_3060_, v___x_3057_, v___x_3058_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref(v___x_3061_);
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3063_ = 1;
v___x_3064_ = l_Lean_registerTraceClass(v___x_3062_, v___x_3063_, v___x_3058_);
return v___x_3064_;
}
else
{
return v___x_3061_;
}
}
else
{
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3066_;
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
