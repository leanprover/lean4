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
LEAN_EXPORT uint8_t l_Lean_Elab_getBetterRef___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getBetterRef___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_214_, lean_object* v_toApplicative_215_, lean_object* v_msgData_216_, lean_object* v_macroStack_217_, lean_object* v_____do__lift_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_Elab_pp_macroStack;
v___x_220_ = l_Lean_Option_get___redArg(v___x_214_, v_____do__lift_218_, v___x_219_);
v___x_221_ = lean_unbox(v___x_220_);
lean_dec(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v_toPure_222_; lean_object* v___x_223_; 
lean_dec(v_macroStack_217_);
v_toPure_222_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_222_);
lean_dec_ref(v_toApplicative_215_);
v___x_223_ = lean_apply_2(v_toPure_222_, lean_box(0), v_msgData_216_);
return v___x_223_;
}
else
{
if (lean_obj_tag(v_macroStack_217_) == 0)
{
lean_object* v_toPure_224_; lean_object* v___x_225_; 
v_toPure_224_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_224_);
lean_dec_ref(v_toApplicative_215_);
v___x_225_ = lean_apply_2(v_toPure_224_, lean_box(0), v_msgData_216_);
return v___x_225_;
}
else
{
lean_object* v_head_226_; lean_object* v_after_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_244_; 
v_head_226_ = lean_ctor_get(v_macroStack_217_, 0);
lean_inc(v_head_226_);
v_after_227_ = lean_ctor_get(v_head_226_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_head_226_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_head_226_, 0);
lean_dec(v_unused_245_);
v___x_229_ = v_head_226_;
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_after_227_);
lean_dec(v_head_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_toPure_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___x_235_; 
v_toPure_231_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_231_);
lean_dec_ref(v_toApplicative_215_);
v___x_232_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_233_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 7);
lean_ctor_set(v___x_229_, 1, v___x_232_);
lean_ctor_set(v___x_229_, 0, v_msgData_216_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_msgData_216_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_232_);
v___x_235_ = v_reuseFailAlloc_243_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_msgData_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_236_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_MessageData_ofSyntax(v_after_227_);
v___x_239_ = l_Lean_indentD(v___x_238_);
v_msgData_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_240_, 0, v___x_237_);
lean_ctor_set(v_msgData_240_, 1, v___x_239_);
v___x_241_ = l_List_foldl___redArg(v___f_233_, v_msgData_240_, v_macroStack_217_);
v___x_242_ = lean_apply_2(v_toPure_231_, lean_box(0), v___x_241_);
return v___x_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_246_, lean_object* v_toApplicative_247_, lean_object* v_msgData_248_, lean_object* v_macroStack_249_, lean_object* v_____do__lift_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_246_, v_toApplicative_247_, v_msgData_248_, v_macroStack_249_, v_____do__lift_250_);
lean_dec_ref(v_____do__lift_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_msgData_254_, lean_object* v_macroStack_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_toApplicative_257_; lean_object* v_toBind_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v___x_256_ = l_Lean_KVMap_instValueBool;
v_toApplicative_257_ = lean_ctor_get(v_inst_252_, 0);
lean_inc_ref(v_toApplicative_257_);
v_toBind_258_ = lean_ctor_get(v_inst_252_, 1);
lean_inc(v_toBind_258_);
lean_dec_ref(v_inst_252_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_259_, 0, v___x_256_);
lean_closure_set(v___f_259_, 1, v_toApplicative_257_);
lean_closure_set(v___f_259_, 2, v_msgData_254_);
lean_closure_set(v___f_259_, 3, v_macroStack_255_);
v___x_260_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v_inst_253_, v___f_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_msgData_264_, lean_object* v_macroStack_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Elab_addMacroStack___redArg(v_inst_262_, v_inst_263_, v_msgData_264_, v_macroStack_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_____r_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_274_ = l_Lean_throwError___redArg(v_inst_270_, v_inst_271_, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_275_, lean_object* v___f_276_, lean_object* v_toApplicative_277_, lean_object* v_____do__lift_278_){
_start:
{
uint8_t v___x_279_; 
lean_inc(v_k_275_);
v___x_279_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_278_, v_k_275_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v_toApplicative_277_);
lean_dec(v_k_275_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_apply_1(v___f_276_, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v_toPure_282_; lean_object* v___x_283_; 
lean_dec(v___f_276_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_277_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_277_);
v___x_283_ = lean_apply_2(v_toPure_282_, lean_box(0), v_k_275_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_284_, lean_object* v___f_285_, lean_object* v_toApplicative_286_, lean_object* v_toBind_287_, lean_object* v_getEnv_288_, lean_object* v_____do__lift_289_){
_start:
{
lean_object* v_k_290_; lean_object* v___f_291_; lean_object* v___x_292_; 
v_k_290_ = l_Lean_mkPrivateName(v_____do__lift_289_, v_k_284_);
v___f_291_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_291_, 0, v_k_290_);
lean_closure_set(v___f_291_, 1, v___f_285_);
lean_closure_set(v___f_291_, 2, v_toApplicative_286_);
v___x_292_ = lean_apply_4(v_toBind_287_, lean_box(0), lean_box(0), v_getEnv_288_, v___f_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_293_, lean_object* v___f_294_, lean_object* v_toApplicative_295_, lean_object* v_toBind_296_, lean_object* v_getEnv_297_, lean_object* v_____do__lift_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_293_, v___f_294_, v_toApplicative_295_, v_toBind_296_, v_getEnv_297_, v_____do__lift_298_);
lean_dec_ref(v_____do__lift_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_300_, lean_object* v_k_301_, lean_object* v_toBind_302_, lean_object* v_getEnv_303_, lean_object* v___f_304_, uint8_t v___x_305_, lean_object* v_____do__lift_306_){
_start:
{
uint8_t v_isExporting_314_; 
v_isExporting_314_ = lean_ctor_get_uint8(v_____do__lift_306_, sizeof(void*)*8);
if (v_isExporting_314_ == 0)
{
goto v___jp_310_;
}
else
{
if (v___x_305_ == 0)
{
lean_dec(v___f_304_);
lean_dec(v_getEnv_303_);
lean_dec(v_toBind_302_);
goto v___jp_307_;
}
else
{
goto v___jp_310_;
}
}
v___jp_307_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_apply_1(v___f_300_, v___x_308_);
return v___x_309_;
}
v___jp_310_:
{
uint8_t v___x_311_; 
v___x_311_ = l_Lean_isPrivateName(v_k_301_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v___f_300_);
v___x_312_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v_getEnv_303_, v___f_304_);
return v___x_312_;
}
else
{
if (v___x_305_ == 0)
{
lean_dec(v___f_304_);
lean_dec(v_getEnv_303_);
lean_dec(v_toBind_302_);
goto v___jp_307_;
}
else
{
lean_object* v___x_313_; 
lean_dec(v___f_300_);
v___x_313_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v_getEnv_303_, v___f_304_);
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_315_, lean_object* v_k_316_, lean_object* v_toBind_317_, lean_object* v_getEnv_318_, lean_object* v___f_319_, lean_object* v___x_320_, lean_object* v_____do__lift_321_){
_start:
{
uint8_t v___x_386__boxed_322_; lean_object* v_res_323_; 
v___x_386__boxed_322_ = lean_unbox(v___x_320_);
v_res_323_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_315_, v_k_316_, v_toBind_317_, v_getEnv_318_, v___f_319_, v___x_386__boxed_322_, v_____do__lift_321_);
lean_dec_ref(v_____do__lift_321_);
lean_dec(v_k_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_324_, lean_object* v___f_325_, lean_object* v_toBind_326_, lean_object* v_getEnv_327_, lean_object* v___f_328_, lean_object* v_toApplicative_329_, lean_object* v_____do__lift_330_){
_start:
{
uint8_t v___x_331_; 
lean_inc(v_k_324_);
v___x_331_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_330_, v_k_324_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___f_333_; lean_object* v___x_334_; 
lean_dec_ref(v_toApplicative_329_);
v___x_332_ = lean_box(v___x_331_);
lean_inc(v_getEnv_327_);
lean_inc(v_toBind_326_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_333_, 0, v___f_325_);
lean_closure_set(v___f_333_, 1, v_k_324_);
lean_closure_set(v___f_333_, 2, v_toBind_326_);
lean_closure_set(v___f_333_, 3, v_getEnv_327_);
lean_closure_set(v___f_333_, 4, v___f_328_);
lean_closure_set(v___f_333_, 5, v___x_332_);
v___x_334_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v_getEnv_327_, v___f_333_);
return v___x_334_;
}
else
{
lean_object* v_toPure_335_; lean_object* v___x_336_; 
lean_dec(v___f_328_);
lean_dec(v_getEnv_327_);
lean_dec(v_toBind_326_);
lean_dec(v___f_325_);
v_toPure_335_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_335_);
lean_dec_ref(v_toApplicative_329_);
v___x_336_ = lean_apply_2(v_toPure_335_, lean_box(0), v_k_324_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_toApplicative_341_; lean_object* v_toBind_342_; lean_object* v_getEnv_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_toApplicative_341_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref_n(v_toApplicative_341_, 2);
v_toBind_342_ = lean_ctor_get(v_inst_337_, 1);
lean_inc_n(v_toBind_342_, 3);
v_getEnv_343_ = lean_ctor_get(v_inst_338_, 0);
lean_inc_n(v_getEnv_343_, 3);
lean_dec_ref(v_inst_338_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_344_, 0, v_inst_337_);
lean_closure_set(v___f_344_, 1, v_inst_339_);
lean_inc_ref(v___f_344_);
lean_inc(v_k_340_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_345_, 0, v_k_340_);
lean_closure_set(v___f_345_, 1, v___f_344_);
lean_closure_set(v___f_345_, 2, v_toApplicative_341_);
lean_closure_set(v___f_345_, 3, v_toBind_342_);
lean_closure_set(v___f_345_, 4, v_getEnv_343_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_346_, 0, v_k_340_);
lean_closure_set(v___f_346_, 1, v___f_344_);
lean_closure_set(v___f_346_, 2, v_toBind_342_);
lean_closure_set(v___f_346_, 3, v_getEnv_343_);
lean_closure_set(v___f_346_, 4, v___f_345_);
lean_closure_set(v___f_346_, 5, v_toApplicative_341_);
v___x_347_ = lean_apply_4(v_toBind_342_, lean_box(0), lean_box(0), v_getEnv_343_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_k_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_k_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_k_357_, lean_object* v_pre_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_354_, v_inst_355_, v_inst_356_, v_k_357_, v_pre_358_, v_x_359_);
lean_dec_ref(v_x_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_k_364_, lean_object* v_x_365_){
_start:
{
switch(lean_obj_tag(v_x_365_))
{
case 1:
{
lean_object* v_toMonadExceptOf_366_; lean_object* v_pre_367_; lean_object* v_tryCatch_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_toMonadExceptOf_366_ = lean_ctor_get(v_inst_363_, 0);
v_pre_367_ = lean_ctor_get(v_x_365_, 0);
v_tryCatch_368_ = lean_ctor_get(v_toMonadExceptOf_366_, 1);
lean_inc(v_tryCatch_368_);
lean_inc(v_pre_367_);
lean_inc(v_k_364_);
lean_inc_ref(v_inst_363_);
lean_inc_ref(v_inst_362_);
lean_inc_ref(v_inst_361_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_369_, 0, v_inst_361_);
lean_closure_set(v___f_369_, 1, v_inst_362_);
lean_closure_set(v___f_369_, 2, v_inst_363_);
lean_closure_set(v___f_369_, 3, v_k_364_);
lean_closure_set(v___f_369_, 4, v_pre_367_);
v___x_370_ = l_Lean_Name_append(v_x_365_, v_k_364_);
v___x_371_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_361_, v_inst_362_, v_inst_363_, v___x_370_);
v___x_372_ = lean_apply_3(v_tryCatch_368_, lean_box(0), v___x_371_, v___f_369_);
return v___x_372_;
}
case 0:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_361_, v_inst_362_, v_inst_363_, v_k_364_);
return v___x_373_;
}
default: 
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_x_365_);
lean_dec(v_k_364_);
lean_dec_ref(v_inst_362_);
v___x_374_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_375_ = l_Lean_throwError___redArg(v_inst_361_, v_inst_363_, v___x_374_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_k_379_, lean_object* v_pre_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_376_, v_inst_377_, v_inst_378_, v_k_379_, v_pre_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_k_387_, lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_384_, v_inst_385_, v_inst_386_, v_k_387_, v_x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_390_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_ctor_set(v___x_395_, 2, v___x_394_);
lean_ctor_set(v___x_395_, 3, v___x_394_);
lean_ctor_set(v___x_395_, 4, v___x_393_);
lean_ctor_set(v___x_395_, 5, v___x_393_);
lean_ctor_set(v___x_395_, 6, v___x_393_);
lean_ctor_set(v___x_395_, 7, v___x_393_);
lean_ctor_set(v___x_395_, 8, v___x_393_);
lean_ctor_set(v___x_395_, 9, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(32u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = ((size_t)5ULL);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_unsigned_to_nat(32u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_400_);
lean_ctor_set(v___x_404_, 3, v___x_400_);
lean_ctor_set_usize(v___x_404_, 4, v___x_399_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(1);
v___x_406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_env_414_; lean_object* v_options_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_413_ = lean_st_ref_get(v___y_411_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_413_);
v_options_415_ = lean_ctor_get(v___y_410_, 2);
v___x_416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_415_);
v___x_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_418_, 0, v_env_414_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_417_);
lean_ctor_set(v___x_418_, 3, v_options_415_);
v___x_419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_msgData_409_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_ref_430_; lean_object* v___x_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_ref_430_ = lean_ctor_get(v___y_427_, 5);
v___x_431_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_426_, v___y_427_, v___y_428_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_ref_430_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_ref_430_);
lean_ctor_set(v___x_436_, 1, v_a_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(lean_object* v_k_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___x_455_; lean_object* v_env_456_; uint8_t v___x_457_; 
v___x_455_ = lean_st_ref_get(v___y_448_);
v_env_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_456_);
lean_dec(v___x_455_);
lean_inc(v_k_446_);
v___x_457_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_456_, v_k_446_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v_env_475_; uint8_t v_isExporting_476_; 
v___x_458_ = lean_st_ref_get(v___y_448_);
v_env_475_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_475_);
lean_dec(v___x_458_);
v_isExporting_476_ = lean_ctor_get_uint8(v_env_475_, sizeof(void*)*8);
lean_dec_ref(v_env_475_);
if (v_isExporting_476_ == 0)
{
goto v___jp_459_;
}
else
{
if (v___x_457_ == 0)
{
lean_dec(v_k_446_);
v___y_451_ = v___y_447_;
v___y_452_ = v___y_448_;
goto v___jp_450_;
}
else
{
goto v___jp_459_;
}
}
v___jp_459_:
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_isPrivateName(v_k_446_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v_env_462_; lean_object* v___x_463_; lean_object* v_env_464_; lean_object* v_k_465_; uint8_t v___x_466_; 
v___x_461_ = lean_st_ref_get(v___y_448_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
v___x_463_ = lean_st_ref_get(v___y_448_);
v_env_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_env_464_);
lean_dec(v___x_463_);
v_k_465_ = l_Lean_mkPrivateName(v_env_462_, v_k_446_);
lean_dec_ref(v_env_462_);
lean_inc(v_k_465_);
v___x_466_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_464_, v_k_465_);
if (v___x_466_ == 0)
{
lean_dec(v_k_465_);
v___y_451_ = v___y_447_;
v___y_452_ = v___y_448_;
goto v___jp_450_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v_k_465_);
return v___x_467_;
}
}
else
{
if (v___x_457_ == 0)
{
lean_dec(v_k_446_);
v___y_451_ = v___y_447_;
v___y_452_ = v___y_448_;
goto v___jp_450_;
}
else
{
lean_object* v___x_468_; lean_object* v_env_469_; lean_object* v___x_470_; lean_object* v_env_471_; lean_object* v_k_472_; uint8_t v___x_473_; 
v___x_468_ = lean_st_ref_get(v___y_448_);
v_env_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_env_469_);
lean_dec(v___x_468_);
v___x_470_ = lean_st_ref_get(v___y_448_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref(v_env_471_);
lean_dec(v___x_470_);
v_k_472_ = l_Lean_mkPrivateName(v_env_469_, v_k_446_);
lean_dec_ref(v_env_469_);
lean_inc(v_k_472_);
v___x_473_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_471_, v_k_472_);
if (v___x_473_ == 0)
{
lean_dec(v_k_472_);
v___y_451_ = v___y_447_;
v___y_452_ = v___y_448_;
goto v___jp_450_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_k_472_);
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_k_446_);
return v___x_477_;
}
v___jp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_454_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_453_, v___y_451_, v___y_452_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(lean_object* v_k_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(lean_object* v_k_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
switch(lean_obj_tag(v_x_484_))
{
case 1:
{
lean_object* v_pre_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_pre_488_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_pre_488_);
lean_inc(v_k_483_);
v___x_489_ = l_Lean_Name_append(v_x_484_, v_k_483_);
v___x_490_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_489_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec(v_pre_488_);
lean_dec(v_k_483_);
return v___x_490_;
}
else
{
lean_object* v_a_491_; uint8_t v___y_493_; uint8_t v___x_495_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
v___x_495_ = l_Lean_Exception_isInterrupt(v_a_491_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; 
v___x_496_ = l_Lean_Exception_isRuntime(v_a_491_);
v___y_493_ = v___x_496_;
goto v___jp_492_;
}
else
{
lean_dec(v_a_491_);
v___y_493_ = v___x_495_;
goto v___jp_492_;
}
v___jp_492_:
{
if (v___y_493_ == 0)
{
lean_dec_ref(v___x_490_);
v_x_484_ = v_pre_488_;
goto _start;
}
else
{
lean_dec(v_pre_488_);
lean_dec(v_k_483_);
return v___x_490_;
}
}
}
}
case 0:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_483_, v___y_485_, v___y_486_);
return v___x_497_;
}
default: 
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_x_484_);
lean_dec(v_k_483_);
v___x_498_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_499_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_498_, v___y_485_, v___y_486_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(lean_object* v_k_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_500_, v_x_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(lean_object* v_k_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_currNamespace_510_; lean_object* v___x_511_; 
v_currNamespace_510_ = lean_ctor_get(v_a_507_, 6);
lean_inc(v_currNamespace_510_);
v___x_511_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_506_, v_currNamespace_510_, v_a_507_, v_a_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(lean_object* v_k_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(lean_object* v_00_u03b1_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(lean_object* v_00_u03b1_523_, lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_523_, v_msg_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* v_defaultParserNamespace_535_, lean_object* v_stx_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Attribute_Builtin_getId(v_stx_536_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___x_551_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc_n(v_a_541_, 2);
lean_dec_ref(v___x_540_);
v___x_551_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_a_541_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_dec(v_a_541_);
lean_dec(v_defaultParserNamespace_535_);
return v___x_551_;
}
else
{
lean_object* v_a_552_; uint8_t v___y_554_; uint8_t v___x_560_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
v___x_560_ = l_Lean_Exception_isInterrupt(v_a_552_);
if (v___x_560_ == 0)
{
uint8_t v___x_561_; 
v___x_561_ = l_Lean_Exception_isRuntime(v_a_552_);
v___y_554_ = v___x_561_;
goto v___jp_553_;
}
else
{
lean_dec(v_a_552_);
v___y_554_ = v___x_560_;
goto v___jp_553_;
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___x_551_);
lean_inc(v_a_541_);
v___x_555_ = l_Lean_Name_append(v_defaultParserNamespace_535_, v_a_541_);
v___x_556_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_555_, v_a_537_, v_a_538_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_dec(v_a_541_);
return v___x_556_;
}
else
{
lean_object* v_a_557_; uint8_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
v___x_558_ = l_Lean_Exception_isInterrupt(v_a_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_Exception_isRuntime(v_a_557_);
v___y_543_ = v___x_556_;
v___y_544_ = v___x_559_;
goto v___jp_542_;
}
else
{
lean_dec(v_a_557_);
v___y_543_ = v___x_556_;
v___y_544_ = v___x_558_;
goto v___jp_542_;
}
}
}
else
{
lean_dec(v_a_541_);
lean_dec(v_defaultParserNamespace_535_);
return v___x_551_;
}
}
}
v___jp_542_:
{
if (v___y_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref(v___y_543_);
v___x_545_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
v___x_546_ = l_Lean_MessageData_ofName(v_a_541_);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_549_, v_a_537_, v_a_538_);
return v___x_550_;
}
else
{
lean_dec(v_a_541_);
return v___y_543_;
}
}
}
else
{
lean_dec(v_defaultParserNamespace_535_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* v_defaultParserNamespace_562_, lean_object* v_stx_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_defaultParserNamespace_562_, v_stx_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object* v_env_572_, lean_object* v_opts_573_, lean_object* v_constName_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1));
v___x_576_ = l_Lean_Environment_evalConstCheck___redArg(v_env_572_, v_opts_573_, v___x_575_, v_constName_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(lean_object* v_env_577_, lean_object* v_opts_578_, lean_object* v_constName_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(v_env_577_, v_opts_578_, v_constName_579_);
lean_dec_ref(v_opts_578_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__8));
v___x_606_ = l_Lean_mkAtom(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__10, &l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10);
v___x_608_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_609_ = lean_array_push(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__15));
v___x_619_ = l_Lean_mkAtom(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__16, &l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16);
v___x_621_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_622_ = lean_array_push(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__17, &l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17);
v___x_624_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__14));
v___x_625_ = lean_box(2);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__18, &l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18);
v___x_628_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__11, &l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11);
v___x_629_ = lean_array_push(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__19, &l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19);
v___x_631_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__9));
v___x_632_ = lean_box(2);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_630_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__20, &l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20);
v___x_635_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_636_ = lean_array_push(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__21, &l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21);
v___x_638_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__7));
v___x_639_ = lean_box(2);
v___x_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
lean_ctor_set(v___x_640_, 2, v___x_637_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__22, &l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22);
v___x_642_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_643_ = lean_array_push(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__23, &l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23);
v___x_645_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__5));
v___x_646_ = lean_box(2);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_644_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__24, &l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24);
v___x_649_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__3));
v___x_650_ = lean_array_push(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__25, &l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25);
v___x_652_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___auto__1___closed__2));
v___x_653_ = lean_box(2);
v___x_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_651_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Elab_mkElabAttribute___auto__1(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_Elab_mkElabAttribute___auto__1___closed__26, &l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once, _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0(uint8_t v_builtin_656_, lean_object* v_declName_657_, lean_object* v_kind_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
if (v_builtin_656_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_declName_657_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_657_, v___y_659_, v___y_660_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(lean_object* v_builtin_665_, lean_object* v_declName_666_, lean_object* v_kind_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_builtin_boxed_671_; lean_object* v_res_672_; 
v_builtin_boxed_671_ = lean_unbox(v_builtin_665_);
v_res_672_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(v_builtin_boxed_671_, v_declName_666_, v_kind_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v_kind_667_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(lean_object* v_t_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; lean_object* v_infoState_677_; uint8_t v_enabled_678_; 
v___x_676_ = lean_st_ref_get(v___y_674_);
v_infoState_677_ = lean_ctor_get(v___x_676_, 7);
lean_inc_ref(v_infoState_677_);
lean_dec(v___x_676_);
v_enabled_678_ = lean_ctor_get_uint8(v_infoState_677_, sizeof(void*)*3);
lean_dec_ref(v_infoState_677_);
if (v_enabled_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v_t_673_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v_infoState_682_; lean_object* v_env_683_; lean_object* v_nextMacroScope_684_; lean_object* v_ngen_685_; lean_object* v_auxDeclNGen_686_; lean_object* v_traceState_687_; lean_object* v_cache_688_; lean_object* v_messages_689_; lean_object* v_snapshotTasks_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_712_; 
v___x_681_ = lean_st_ref_take(v___y_674_);
v_infoState_682_ = lean_ctor_get(v___x_681_, 7);
v_env_683_ = lean_ctor_get(v___x_681_, 0);
v_nextMacroScope_684_ = lean_ctor_get(v___x_681_, 1);
v_ngen_685_ = lean_ctor_get(v___x_681_, 2);
v_auxDeclNGen_686_ = lean_ctor_get(v___x_681_, 3);
v_traceState_687_ = lean_ctor_get(v___x_681_, 4);
v_cache_688_ = lean_ctor_get(v___x_681_, 5);
v_messages_689_ = lean_ctor_get(v___x_681_, 6);
v_snapshotTasks_690_ = lean_ctor_get(v___x_681_, 8);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_712_ == 0)
{
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_712_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snapshotTasks_690_);
lean_inc(v_infoState_682_);
lean_inc(v_messages_689_);
lean_inc(v_cache_688_);
lean_inc(v_traceState_687_);
lean_inc(v_auxDeclNGen_686_);
lean_inc(v_ngen_685_);
lean_inc(v_nextMacroScope_684_);
lean_inc(v_env_683_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_712_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v_enabled_694_; lean_object* v_assignment_695_; lean_object* v_lazyAssignment_696_; lean_object* v_trees_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_711_; 
v_enabled_694_ = lean_ctor_get_uint8(v_infoState_682_, sizeof(void*)*3);
v_assignment_695_ = lean_ctor_get(v_infoState_682_, 0);
v_lazyAssignment_696_ = lean_ctor_get(v_infoState_682_, 1);
v_trees_697_ = lean_ctor_get(v_infoState_682_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_infoState_682_);
if (v_isSharedCheck_711_ == 0)
{
v___x_699_ = v_infoState_682_;
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_trees_697_);
lean_inc(v_lazyAssignment_696_);
lean_inc(v_assignment_695_);
lean_dec(v_infoState_682_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = l_Lean_PersistentArray_push___redArg(v_trees_697_, v_t_673_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_assignment_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_lazyAssignment_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v___x_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*3, v_enabled_694_);
v___x_703_ = v_reuseFailAlloc_710_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 7, v___x_703_);
v___x_705_ = v___x_692_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_env_683_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_nextMacroScope_684_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_ngen_685_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_auxDeclNGen_686_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_traceState_687_);
lean_ctor_set(v_reuseFailAlloc_709_, 5, v_cache_688_);
lean_ctor_set(v_reuseFailAlloc_709_, 6, v_messages_689_);
lean_ctor_set(v_reuseFailAlloc_709_, 7, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 8, v_snapshotTasks_690_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_st_ref_set(v___y_674_, v___x_705_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_713_, v___y_714_);
lean_dec(v___y_714_);
return v_res_716_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(32u);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_720_ = ((size_t)5ULL);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_unsigned_to_nat(32u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
v___x_725_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_721_);
lean_ctor_set(v___x_725_, 3, v___x_721_);
lean_ctor_set_usize(v___x_725_, 4, v___x_720_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(lean_object* v_t_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v_infoState_731_; uint8_t v_enabled_732_; 
v___x_730_ = lean_st_ref_get(v___y_728_);
v_infoState_731_ = lean_ctor_get(v___x_730_, 7);
lean_inc_ref(v_infoState_731_);
lean_dec(v___x_730_);
v_enabled_732_ = lean_ctor_get_uint8(v_infoState_731_, sizeof(void*)*3);
lean_dec_ref(v_infoState_731_);
if (v_enabled_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec_ref(v_t_726_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v_t_726_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_736_, v___y_728_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(lean_object* v_t_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(lean_object* v_msg_764_, lean_object* v_declHint_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_env_769_; uint8_t v___x_770_; 
v___x_768_ = lean_st_ref_get(v___y_766_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_769_);
lean_dec(v___x_768_);
v___x_770_ = l_Lean_Name_isAnonymous(v_declHint_765_);
if (v___x_770_ == 0)
{
uint8_t v_isExporting_771_; 
v_isExporting_771_ = lean_ctor_get_uint8(v_env_769_, sizeof(void*)*8);
if (v_isExporting_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v_env_769_);
lean_dec(v_declHint_765_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_msg_764_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; 
lean_inc_ref(v_env_769_);
v___x_773_ = l_Lean_Environment_setExporting(v_env_769_, v___x_770_);
lean_inc(v_declHint_765_);
lean_inc_ref(v___x_773_);
v___x_774_ = l_Lean_Environment_contains(v___x_773_, v_declHint_765_, v_isExporting_771_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec_ref(v___x_773_);
lean_dec_ref(v_env_769_);
lean_dec(v_declHint_765_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_msg_764_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_c_781_; lean_object* v___x_782_; 
v___x_776_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_777_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_778_ = l_Lean_Options_empty;
v___x_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_779_, 0, v___x_773_);
lean_ctor_set(v___x_779_, 1, v___x_776_);
lean_ctor_set(v___x_779_, 2, v___x_777_);
lean_ctor_set(v___x_779_, 3, v___x_778_);
lean_inc(v_declHint_765_);
v___x_780_ = l_Lean_MessageData_ofConstName(v_declHint_765_, v___x_770_);
v_c_781_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_781_, 0, v___x_779_);
lean_ctor_set(v_c_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_769_, v_declHint_765_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_env_769_);
lean_dec(v_declHint_765_);
v___x_783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_c_781_);
v___x_785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_MessageData_note(v___x_786_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v_msg_764_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_825_; 
v_val_790_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_825_ == 0)
{
v___x_792_ = v___x_782_;
v_isShared_793_ = v_isSharedCheck_825_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_val_790_);
lean_dec(v___x_782_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_825_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_mod_797_; uint8_t v___x_798_; 
v___x_794_ = lean_box(0);
v___x_795_ = l_Lean_Environment_header(v_env_769_);
lean_dec_ref(v_env_769_);
v___x_796_ = l_Lean_EnvironmentHeader_moduleNames(v___x_795_);
v_mod_797_ = lean_array_get(v___x_794_, v___x_796_, v_val_790_);
lean_dec(v_val_790_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_isPrivateName(v_declHint_765_);
lean_dec(v_declHint_765_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_c_781_);
v___x_801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_MessageData_ofName(v_mod_797_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_MessageData_note(v___x_806_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v_msg_764_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 0);
lean_ctor_set(v___x_792_, 0, v___x_808_);
v___x_810_ = v___x_792_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_c_781_);
v___x_814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofName(v_mod_797_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_MessageData_note(v___x_819_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v_msg_764_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 0);
lean_ctor_set(v___x_792_, 0, v___x_821_);
v___x_823_ = v___x_792_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_826_; 
lean_dec_ref(v_env_769_);
lean_dec(v_declHint_765_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_msg_764_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(lean_object* v_msg_827_, lean_object* v_declHint_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_827_, v_declHint_828_, v___y_829_);
lean_dec(v___y_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(lean_object* v_msg_832_, lean_object* v_declHint_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_847_; 
v___x_837_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_832_, v_declHint_833_, v___y_835_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = l_Lean_unknownIdentifierMessageTag;
v___x_843_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v_a_838_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_845_ = v___x_840_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(lean_object* v_msg_848_, lean_object* v_declHint_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_848_, v_declHint_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_854_, lean_object* v_msg_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_fileName_859_; lean_object* v_fileMap_860_; lean_object* v_options_861_; lean_object* v_currRecDepth_862_; lean_object* v_maxRecDepth_863_; lean_object* v_ref_864_; lean_object* v_currNamespace_865_; lean_object* v_openDecls_866_; lean_object* v_initHeartbeats_867_; lean_object* v_maxHeartbeats_868_; lean_object* v_quotContext_869_; lean_object* v_currMacroScope_870_; uint8_t v_diag_871_; lean_object* v_cancelTk_x3f_872_; uint8_t v_suppressElabErrors_873_; lean_object* v_inheritedTraceOptions_874_; lean_object* v_ref_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_fileName_859_ = lean_ctor_get(v___y_856_, 0);
v_fileMap_860_ = lean_ctor_get(v___y_856_, 1);
v_options_861_ = lean_ctor_get(v___y_856_, 2);
v_currRecDepth_862_ = lean_ctor_get(v___y_856_, 3);
v_maxRecDepth_863_ = lean_ctor_get(v___y_856_, 4);
v_ref_864_ = lean_ctor_get(v___y_856_, 5);
v_currNamespace_865_ = lean_ctor_get(v___y_856_, 6);
v_openDecls_866_ = lean_ctor_get(v___y_856_, 7);
v_initHeartbeats_867_ = lean_ctor_get(v___y_856_, 8);
v_maxHeartbeats_868_ = lean_ctor_get(v___y_856_, 9);
v_quotContext_869_ = lean_ctor_get(v___y_856_, 10);
v_currMacroScope_870_ = lean_ctor_get(v___y_856_, 11);
v_diag_871_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*14);
v_cancelTk_x3f_872_ = lean_ctor_get(v___y_856_, 12);
v_suppressElabErrors_873_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_874_ = lean_ctor_get(v___y_856_, 13);
v_ref_875_ = l_Lean_replaceRef(v_ref_854_, v_ref_864_);
lean_inc_ref(v_inheritedTraceOptions_874_);
lean_inc(v_cancelTk_x3f_872_);
lean_inc(v_currMacroScope_870_);
lean_inc(v_quotContext_869_);
lean_inc(v_maxHeartbeats_868_);
lean_inc(v_initHeartbeats_867_);
lean_inc(v_openDecls_866_);
lean_inc(v_currNamespace_865_);
lean_inc(v_maxRecDepth_863_);
lean_inc(v_currRecDepth_862_);
lean_inc_ref(v_options_861_);
lean_inc_ref(v_fileMap_860_);
lean_inc_ref(v_fileName_859_);
v___x_876_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_876_, 0, v_fileName_859_);
lean_ctor_set(v___x_876_, 1, v_fileMap_860_);
lean_ctor_set(v___x_876_, 2, v_options_861_);
lean_ctor_set(v___x_876_, 3, v_currRecDepth_862_);
lean_ctor_set(v___x_876_, 4, v_maxRecDepth_863_);
lean_ctor_set(v___x_876_, 5, v_ref_875_);
lean_ctor_set(v___x_876_, 6, v_currNamespace_865_);
lean_ctor_set(v___x_876_, 7, v_openDecls_866_);
lean_ctor_set(v___x_876_, 8, v_initHeartbeats_867_);
lean_ctor_set(v___x_876_, 9, v_maxHeartbeats_868_);
lean_ctor_set(v___x_876_, 10, v_quotContext_869_);
lean_ctor_set(v___x_876_, 11, v_currMacroScope_870_);
lean_ctor_set(v___x_876_, 12, v_cancelTk_x3f_872_);
lean_ctor_set(v___x_876_, 13, v_inheritedTraceOptions_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*14, v_diag_871_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*14 + 1, v_suppressElabErrors_873_);
v___x_877_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_855_, v___x_876_, v___y_857_);
lean_dec_ref(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_878_, v_msg_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_ref_878_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_884_, lean_object* v_msg_885_, lean_object* v_declHint_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_a_891_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_885_, v_declHint_886_, v___y_887_, v___y_888_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_884_, v_a_891_, v___y_887_, v___y_888_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_893_, lean_object* v_msg_894_, lean_object* v_declHint_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_893_, v_msg_894_, v_declHint_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_ref_893_);
return v_res_899_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_903_, lean_object* v_constName_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_908_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_909_ = 0;
lean_inc(v_constName_904_);
v___x_910_ = l_Lean_MessageData_ofConstName(v_constName_904_, v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_908_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_903_, v___x_913_, v_constName_904_, v___y_905_, v___y_906_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_915_, lean_object* v_constName_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_915_, v_constName_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v_ref_915_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_ref_925_; lean_object* v___x_926_; 
v_ref_925_ = lean_ctor_get(v___y_922_, 5);
v___x_926_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_925_, v_constName_921_, v___y_922_, v___y_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v_env_937_; uint8_t v___x_938_; lean_object* v___x_939_; 
v___x_936_ = lean_st_ref_get(v___y_934_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_env_937_);
lean_dec(v___x_936_);
v___x_938_ = 0;
lean_inc(v_constName_932_);
v___x_939_ = l_Lean_Environment_findConstVal_x3f(v_env_937_, v_constName_932_, v___x_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_932_, v___y_933_, v___y_934_);
return v___x_940_;
}
else
{
lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_constName_932_);
v_val_941_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_val_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
if (lean_obj_tag(v_a_954_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = l_List_reverse___redArg(v_a_955_);
return v___x_956_;
}
else
{
lean_object* v_head_957_; lean_object* v_tail_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v_head_957_ = lean_ctor_get(v_a_954_, 0);
v_tail_958_ = lean_ctor_get(v_a_954_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_967_ == 0)
{
v___x_960_ = v_a_954_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_tail_958_);
lean_inc(v_head_957_);
lean_dec(v_a_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Lean_mkLevelParam(v_head_957_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_955_);
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_955_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v_a_954_ = v_tail_958_;
v_a_955_ = v___x_964_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc(v_constName_968_);
v___x_972_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_984_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_984_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_984_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_984_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_levelParams_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v_levelParams_977_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_levelParams_977_);
lean_dec(v_a_973_);
v___x_978_ = lean_box(0);
v___x_979_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_977_, v___x_978_);
v___x_980_ = l_Lean_mkConst(v_constName_968_, v___x_979_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_980_);
v___x_982_ = v___x_975_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_constName_968_);
v_a_985_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_972_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_972_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_998_, lean_object* v_n_999_, lean_object* v_expectedType_x3f_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_999_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_stx_998_);
v___x_1008_ = l_Lean_LocalContext_empty;
v___x_1009_ = 0;
v___x_1010_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1008_);
lean_ctor_set(v___x_1010_, 2, v_expectedType_x3f_1000_);
lean_ctor_set(v___x_1010_, 3, v_a_1005_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*4, v___x_1009_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*4 + 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
v___x_1012_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1011_, v___y_1001_, v___y_1002_);
return v___x_1012_;
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_expectedType_x3f_1000_);
lean_dec(v_stx_998_);
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1021_, lean_object* v_n_1022_, lean_object* v_expectedType_x3f_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1021_, v_n_1022_, v_expectedType_x3f_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1028_, lean_object* v_i_1029_, lean_object* v_k_1030_){
_start:
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = lean_array_get_size(v_keys_1028_);
v___x_1032_ = lean_nat_dec_lt(v_i_1029_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec(v_i_1029_);
return v___x_1032_;
}
else
{
lean_object* v_k_x27_1033_; uint8_t v___x_1034_; 
v_k_x27_1033_ = lean_array_fget_borrowed(v_keys_1028_, v_i_1029_);
v___x_1034_ = l_Lean_instBEqExtraModUse_beq(v_k_1030_, v_k_x27_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_add(v_i_1029_, v___x_1035_);
lean_dec(v_i_1029_);
v_i_1029_ = v___x_1036_;
goto _start;
}
else
{
lean_dec(v_i_1029_);
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1038_, lean_object* v_i_1039_, lean_object* v_k_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1038_, v_i_1039_, v_k_1040_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_keys_1038_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; 
v___x_1043_ = ((size_t)5ULL);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_shift_left(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1048_ = lean_usize_sub(v___x_1047_, v___x_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1049_, size_t v_x_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1049_) == 0)
{
lean_object* v_es_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v_j_1057_; lean_object* v___x_1058_; 
v_es_1052_ = lean_ctor_get(v_x_1049_, 0);
v___x_1053_ = lean_box(2);
v___x_1054_ = ((size_t)5ULL);
v___x_1055_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1056_ = lean_usize_land(v_x_1050_, v___x_1055_);
v_j_1057_ = lean_usize_to_nat(v___x_1056_);
v___x_1058_ = lean_array_get_borrowed(v___x_1053_, v_es_1052_, v_j_1057_);
lean_dec(v_j_1057_);
switch(lean_obj_tag(v___x_1058_))
{
case 0:
{
lean_object* v_key_1059_; uint8_t v___x_1060_; 
v_key_1059_ = lean_ctor_get(v___x_1058_, 0);
v___x_1060_ = l_Lean_instBEqExtraModUse_beq(v_x_1051_, v_key_1059_);
return v___x_1060_;
}
case 1:
{
lean_object* v_node_1061_; size_t v___x_1062_; 
v_node_1061_ = lean_ctor_get(v___x_1058_, 0);
v___x_1062_ = lean_usize_shift_right(v_x_1050_, v___x_1054_);
v_x_1049_ = v_node_1061_;
v_x_1050_ = v___x_1062_;
goto _start;
}
default: 
{
uint8_t v___x_1064_; 
v___x_1064_ = 0;
return v___x_1064_;
}
}
}
else
{
lean_object* v_ks_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_ks_1065_ = lean_ctor_get(v_x_1049_, 0);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1065_, v___x_1066_, v_x_1051_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
size_t v_x_6763__boxed_1071_; uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_x_6763__boxed_1071_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1072_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1068_, v_x_6763__boxed_1071_, v_x_1070_);
lean_dec_ref(v_x_1070_);
lean_dec_ref(v_x_1068_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
uint64_t v___x_1076_; size_t v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = l_Lean_instHashableExtraModUse_hash(v_x_1075_);
v___x_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1074_, v___x_1077_, v_x_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1079_, v_x_1080_);
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1079_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1083_; double v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_float_of_nat(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_ref_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1139_; 
v_ref_1093_ = lean_ctor_get(v___y_1090_, 5);
v___x_1094_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1089_, v___y_1090_, v___y_1091_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1139_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1139_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v_traceState_1100_; lean_object* v_env_1101_; lean_object* v_nextMacroScope_1102_; lean_object* v_ngen_1103_; lean_object* v_auxDeclNGen_1104_; lean_object* v_cache_1105_; lean_object* v_messages_1106_; lean_object* v_infoState_1107_; lean_object* v_snapshotTasks_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1138_; 
v___x_1099_ = lean_st_ref_take(v___y_1091_);
v_traceState_1100_ = lean_ctor_get(v___x_1099_, 4);
v_env_1101_ = lean_ctor_get(v___x_1099_, 0);
v_nextMacroScope_1102_ = lean_ctor_get(v___x_1099_, 1);
v_ngen_1103_ = lean_ctor_get(v___x_1099_, 2);
v_auxDeclNGen_1104_ = lean_ctor_get(v___x_1099_, 3);
v_cache_1105_ = lean_ctor_get(v___x_1099_, 5);
v_messages_1106_ = lean_ctor_get(v___x_1099_, 6);
v_infoState_1107_ = lean_ctor_get(v___x_1099_, 7);
v_snapshotTasks_1108_ = lean_ctor_get(v___x_1099_, 8);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1138_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snapshotTasks_1108_);
lean_inc(v_infoState_1107_);
lean_inc(v_messages_1106_);
lean_inc(v_cache_1105_);
lean_inc(v_traceState_1100_);
lean_inc(v_auxDeclNGen_1104_);
lean_inc(v_ngen_1103_);
lean_inc(v_nextMacroScope_1102_);
lean_inc(v_env_1101_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1138_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint64_t v_tid_1112_; lean_object* v_traces_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1137_; 
v_tid_1112_ = lean_ctor_get_uint64(v_traceState_1100_, sizeof(void*)*1);
v_traces_1113_ = lean_ctor_get(v_traceState_1100_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_traceState_1100_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1115_ = v_traceState_1100_;
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_traces_1113_);
lean_dec(v_traceState_1100_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; double v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1119_ = 0;
v___x_1120_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1121_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1121_, 0, v_cls_1088_);
lean_ctor_set(v___x_1121_, 1, v___x_1117_);
lean_ctor_set(v___x_1121_, 2, v___x_1120_);
lean_ctor_set_float(v___x_1121_, sizeof(void*)*3, v___x_1118_);
lean_ctor_set_float(v___x_1121_, sizeof(void*)*3 + 8, v___x_1118_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*3 + 16, v___x_1119_);
v___x_1122_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1123_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v_a_1095_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
lean_inc(v_ref_1093_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_ref_1093_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_PersistentArray_push___redArg(v_traces_1113_, v___x_1124_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1125_);
v___x_1127_ = v___x_1115_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1125_);
lean_ctor_set_uint64(v_reuseFailAlloc_1136_, sizeof(void*)*1, v_tid_1112_);
v___x_1127_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 4, v___x_1127_);
v___x_1129_ = v___x_1110_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_env_1101_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_nextMacroScope_1102_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_ngen_1103_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_auxDeclNGen_1104_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_cache_1105_);
lean_ctor_set(v_reuseFailAlloc_1135_, 6, v_messages_1106_);
lean_ctor_set(v_reuseFailAlloc_1135_, 7, v_infoState_1107_);
lean_ctor_set(v_reuseFailAlloc_1135_, 8, v_snapshotTasks_1108_);
v___x_1129_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1130_ = lean_st_ref_set(v___y_1091_, v___x_1129_);
v___x_1131_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1131_);
v___x_1133_ = v___x_1097_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1140_, lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1140_, v_msg_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1145_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1));
v___x_1149_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0));
v___x_1150_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_cls_1170_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1171_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1172_ = l_Lean_Name_append(v___x_1171_, v_cls_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1183_, uint8_t v_isMeta_1184_, lean_object* v_hint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; uint8_t v_isExporting_1191_; lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; lean_object* v_entry_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___y_1200_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1189_ = lean_st_ref_get(v___y_1187_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_env_1190_);
lean_dec(v___x_1189_);
v_isExporting_1191_ = lean_ctor_get_uint8(v_env_1190_, sizeof(void*)*8);
lean_dec_ref(v_env_1190_);
v___x_1192_ = lean_st_ref_get(v___y_1187_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
lean_inc(v_mod_1183_);
v_entry_1195_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1195_, 0, v_mod_1183_);
lean_ctor_set_uint8(v_entry_1195_, sizeof(void*)*1, v_isExporting_1191_);
lean_ctor_set_uint8(v_entry_1195_, sizeof(void*)*1 + 1, v_isMeta_1184_);
v___x_1196_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1197_ = lean_box(1);
v___x_1198_ = lean_box(0);
v___x_1225_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1194_, v___x_1196_, v_env_1193_, v___x_1197_, v___x_1198_);
v___x_1226_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1225_, v_entry_1195_);
lean_dec(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v_options_1227_; uint8_t v_hasTrace_1228_; 
v_options_1227_ = lean_ctor_get(v___y_1186_, 2);
v_hasTrace_1228_ = lean_ctor_get_uint8(v_options_1227_, sizeof(void*)*1);
if (v_hasTrace_1228_ == 0)
{
lean_dec(v_hint_1185_);
lean_dec(v_mod_1183_);
v___y_1200_ = v___y_1187_;
goto v___jp_1199_;
}
else
{
lean_object* v_inheritedTraceOptions_1229_; lean_object* v_cls_1230_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_inheritedTraceOptions_1229_ = lean_ctor_get(v___y_1186_, 13);
v_cls_1230_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1250_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1229_, v_options_1227_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_hint_1185_);
lean_dec(v_mod_1183_);
v___y_1200_ = v___y_1187_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1252_; lean_object* v___y_1254_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
if (v_isExporting_1191_ == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22));
v___y_1254_ = v___x_1261_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1262_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23));
v___y_1254_ = v___x_1262_;
goto v___jp_1253_;
}
v___jp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_inc_ref(v___y_1254_);
v___x_1255_ = l_Lean_stringToMessageData(v___y_1254_);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1252_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
if (v_isMeta_1184_ == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1237_ = v___x_1258_;
v___y_1238_ = v___x_1259_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21));
v___y_1237_ = v___x_1258_;
v___y_1238_ = v___x_1260_;
goto v___jp_1236_;
}
}
}
v___jp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___y_1232_);
lean_ctor_set(v___x_1234_, 1, v___y_1233_);
v___x_1235_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1230_, v___x_1234_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_dec_ref(v___x_1235_);
v___y_1200_ = v___y_1187_;
goto v___jp_1199_;
}
else
{
lean_dec_ref(v_entry_1195_);
return v___x_1235_;
}
}
v___jp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
lean_inc_ref(v___y_1238_);
v___x_1239_ = l_Lean_stringToMessageData(v___y_1238_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_MessageData_ofName(v_mod_1183_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_Name_isAnonymous(v_hint_1185_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
v___x_1247_ = l_Lean_MessageData_ofName(v_hint_1185_);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___y_1232_ = v___x_1244_;
v___y_1233_ = v___x_1248_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1249_; 
lean_dec(v_hint_1185_);
v___x_1249_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___y_1232_ = v___x_1244_;
v___y_1233_ = v___x_1249_;
goto v___jp_1231_;
}
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v_entry_1195_);
lean_dec(v_hint_1185_);
lean_dec(v_mod_1183_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
v___jp_1199_:
{
lean_object* v___x_1201_; lean_object* v_toEnvExtension_1202_; lean_object* v_env_1203_; lean_object* v_nextMacroScope_1204_; lean_object* v_ngen_1205_; lean_object* v_auxDeclNGen_1206_; lean_object* v_traceState_1207_; lean_object* v_messages_1208_; lean_object* v_infoState_1209_; lean_object* v_snapshotTasks_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1223_; 
v___x_1201_ = lean_st_ref_take(v___y_1200_);
v_toEnvExtension_1202_ = lean_ctor_get(v___x_1196_, 0);
v_env_1203_ = lean_ctor_get(v___x_1201_, 0);
v_nextMacroScope_1204_ = lean_ctor_get(v___x_1201_, 1);
v_ngen_1205_ = lean_ctor_get(v___x_1201_, 2);
v_auxDeclNGen_1206_ = lean_ctor_get(v___x_1201_, 3);
v_traceState_1207_ = lean_ctor_get(v___x_1201_, 4);
v_messages_1208_ = lean_ctor_get(v___x_1201_, 6);
v_infoState_1209_ = lean_ctor_get(v___x_1201_, 7);
v_snapshotTasks_1210_ = lean_ctor_get(v___x_1201_, 8);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1201_, 5);
lean_dec(v_unused_1224_);
v___x_1212_ = v___x_1201_;
v_isShared_1213_ = v_isSharedCheck_1223_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_snapshotTasks_1210_);
lean_inc(v_infoState_1209_);
lean_inc(v_messages_1208_);
lean_inc(v_traceState_1207_);
lean_inc(v_auxDeclNGen_1206_);
lean_inc(v_ngen_1205_);
lean_inc(v_nextMacroScope_1204_);
lean_inc(v_env_1203_);
lean_dec(v___x_1201_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1223_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_asyncMode_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v_asyncMode_1214_ = lean_ctor_get(v_toEnvExtension_1202_, 2);
v___x_1215_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1196_, v_env_1203_, v_entry_1195_, v_asyncMode_1214_, v___x_1198_);
v___x_1216_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 5, v___x_1216_);
lean_ctor_set(v___x_1212_, 0, v___x_1215_);
v___x_1218_ = v___x_1212_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_nextMacroScope_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_ngen_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_auxDeclNGen_1206_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_traceState_1207_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1222_, 6, v_messages_1208_);
lean_ctor_set(v_reuseFailAlloc_1222_, 7, v_infoState_1209_);
lean_ctor_set(v_reuseFailAlloc_1222_, 8, v_snapshotTasks_1210_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_st_ref_set(v___y_1200_, v___x_1218_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1265_, lean_object* v_isMeta_1266_, lean_object* v_hint_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v_isMeta_boxed_1271_; lean_object* v_res_1272_; 
v_isMeta_boxed_1271_ = lean_unbox(v_isMeta_1266_);
v_res_1272_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1265_, v_isMeta_boxed_1271_, v_hint_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1273_, lean_object* v_declName_1274_, lean_object* v_as_1275_, size_t v_sz_1276_, size_t v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_lt(v_i_1277_, v_sz_1276_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v_declName_1274_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1278_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v_modules_1285_; lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v_toImport_1289_; lean_object* v_module_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1284_ = l_Lean_Environment_header(v___x_1273_);
v_modules_1285_ = lean_ctor_get(v___x_1284_, 3);
lean_inc_ref(v_modules_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1287_ = lean_array_uget_borrowed(v_as_1275_, v_i_1277_);
v___x_1288_ = lean_array_get(v___x_1286_, v_modules_1285_, v_a_1287_);
lean_dec_ref(v_modules_1285_);
v_toImport_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_toImport_1289_);
lean_dec(v___x_1288_);
v_module_1290_ = lean_ctor_get(v_toImport_1289_, 0);
lean_inc(v_module_1290_);
lean_dec_ref(v_toImport_1289_);
v___x_1291_ = 0;
lean_inc(v_declName_1274_);
v___x_1292_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1290_, v___x_1291_, v_declName_1274_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; 
lean_dec_ref(v___x_1292_);
v___x_1293_ = lean_box(0);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1277_, v___x_1294_);
v_i_1277_ = v___x_1295_;
v_b_1278_ = v___x_1293_;
goto _start;
}
else
{
lean_dec(v_declName_1274_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1297_, lean_object* v_declName_1298_, lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1297_, v_declName_1298_, v_as_1299_, v_sz_boxed_1306_, v_i_boxed_1307_, v_b_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_as_1299_);
lean_dec_ref(v___x_1297_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
else
{
lean_object* v_key_1312_; lean_object* v_value_1313_; lean_object* v_tail_1314_; uint8_t v___x_1315_; 
v_key_1312_ = lean_ctor_get(v_x_1310_, 0);
v_value_1313_ = lean_ctor_get(v_x_1310_, 1);
v_tail_1314_ = lean_ctor_get(v_x_1310_, 2);
v___x_1315_ = lean_name_eq(v_key_1312_, v_a_1309_);
if (v___x_1315_ == 0)
{
v_x_1310_ = v_tail_1314_;
goto _start;
}
else
{
lean_object* v___x_1317_; 
lean_inc(v_value_1313_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_value_1313_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1318_, v_x_1319_);
lean_dec(v_x_1319_);
lean_dec(v_a_1318_);
return v_res_1320_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1321_; uint64_t v___x_1322_; 
v___x_1321_ = lean_unsigned_to_nat(1723u);
v___x_1322_ = lean_uint64_of_nat(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_buckets_1325_; lean_object* v___x_1326_; uint64_t v___y_1328_; 
v_buckets_1325_ = lean_ctor_get(v_m_1323_, 1);
v___x_1326_ = lean_array_get_size(v_buckets_1325_);
if (lean_obj_tag(v_a_1324_) == 0)
{
uint64_t v___x_1342_; 
v___x_1342_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
v___y_1328_ = v___x_1342_;
goto v___jp_1327_;
}
else
{
uint64_t v_hash_1343_; 
v_hash_1343_ = lean_ctor_get_uint64(v_a_1324_, sizeof(void*)*2);
v___y_1328_ = v_hash_1343_;
goto v___jp_1327_;
}
v___jp_1327_:
{
uint64_t v___x_1329_; uint64_t v___x_1330_; uint64_t v_fold_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; uint64_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1329_ = 32ULL;
v___x_1330_ = lean_uint64_shift_right(v___y_1328_, v___x_1329_);
v_fold_1331_ = lean_uint64_xor(v___y_1328_, v___x_1330_);
v___x_1332_ = 16ULL;
v___x_1333_ = lean_uint64_shift_right(v_fold_1331_, v___x_1332_);
v___x_1334_ = lean_uint64_xor(v_fold_1331_, v___x_1333_);
v___x_1335_ = lean_uint64_to_usize(v___x_1334_);
v___x_1336_ = lean_usize_of_nat(v___x_1326_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_sub(v___x_1336_, v___x_1337_);
v___x_1339_ = lean_usize_land(v___x_1335_, v___x_1338_);
v___x_1340_ = lean_array_uget_borrowed(v_buckets_1325_, v___x_1339_);
v___x_1341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1324_, v___x_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_m_1344_);
return v_res_1346_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___x_1350_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0));
v___x_1351_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1350_, v___x_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1354_, uint8_t v_isMeta_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v_env_1363_; lean_object* v___y_1365_; lean_object* v___x_1378_; 
v___x_1359_ = lean_st_ref_get(v___y_1357_);
v_env_1363_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_ref(v_env_1363_);
lean_dec(v___x_1359_);
v___x_1378_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1363_, v_declName_1354_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_dec_ref(v_env_1363_);
lean_dec(v_declName_1354_);
goto v___jp_1360_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; lean_object* v_modules_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_val_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = l_Lean_Environment_header(v_env_1363_);
v_modules_1381_ = lean_ctor_get(v___x_1380_, 3);
lean_inc_ref(v_modules_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_array_get_size(v_modules_1381_);
v___x_1383_ = lean_nat_dec_lt(v_val_1379_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_modules_1381_);
lean_dec(v_val_1379_);
lean_dec_ref(v_env_1363_);
lean_dec(v_declName_1354_);
goto v___jp_1360_;
}
else
{
lean_object* v___x_1384_; lean_object* v_env_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___y_1389_; 
v___x_1384_ = lean_st_ref_get(v___y_1357_);
v_env_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc_ref(v_env_1385_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
v___x_1387_ = lean_array_fget(v_modules_1381_, v_val_1379_);
lean_dec(v_val_1379_);
lean_dec_ref(v_modules_1381_);
if (v_isMeta_1355_ == 0)
{
lean_dec_ref(v_env_1385_);
v___y_1389_ = v_isMeta_1355_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1400_; 
lean_inc(v_declName_1354_);
v___x_1400_ = l_Lean_isMarkedMeta(v_env_1385_, v_declName_1354_);
if (v___x_1400_ == 0)
{
v___y_1389_ = v_isMeta_1355_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = 0;
v___y_1389_ = v___x_1401_;
goto v___jp_1388_;
}
}
v___jp_1388_:
{
lean_object* v_toImport_1390_; lean_object* v_module_1391_; lean_object* v___x_1392_; 
v_toImport_1390_ = lean_ctor_get(v___x_1387_, 0);
lean_inc_ref(v_toImport_1390_);
lean_dec(v___x_1387_);
v_module_1391_ = lean_ctor_get(v_toImport_1390_, 0);
lean_inc(v_module_1391_);
lean_dec_ref(v_toImport_1390_);
lean_inc(v_declName_1354_);
v___x_1392_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1391_, v___y_1389_, v_declName_1354_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v___x_1392_);
v___x_1393_ = l_Lean_indirectModUseExt;
v___x_1394_ = lean_box(1);
v___x_1395_ = lean_box(0);
lean_inc_ref(v_env_1363_);
v___x_1396_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1386_, v___x_1393_, v_env_1363_, v___x_1394_, v___x_1395_);
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1396_, v_declName_1354_);
lean_dec(v___x_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3));
v___y_1365_ = v___x_1398_;
goto v___jp_1364_;
}
else
{
lean_object* v_val_1399_; 
v_val_1399_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1399_);
lean_dec_ref(v___x_1397_);
v___y_1365_ = v_val_1399_;
goto v___jp_1364_;
}
}
else
{
lean_dec_ref(v_env_1363_);
lean_dec(v_declName_1354_);
return v___x_1392_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
v___jp_1364_:
{
lean_object* v___x_1366_; size_t v_sz_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_box(0);
v_sz_1367_ = lean_array_size(v___y_1365_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1363_, v_declName_1354_, v___y_1365_, v_sz_1367_, v___x_1368_, v___x_1366_, v___y_1356_, v___y_1357_);
lean_dec_ref(v___y_1365_);
lean_dec_ref(v_env_1363_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1377_);
v___x_1371_ = v___x_1369_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v___x_1369_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1366_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1366_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1402_, lean_object* v_isMeta_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_isMeta_boxed_1407_; lean_object* v_res_1408_; 
v_isMeta_boxed_1407_ = lean_unbox(v_isMeta_1403_);
v_res_1408_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1402_, v_isMeta_boxed_1407_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1409_, uint8_t v_x_1410_, lean_object* v_stx_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
lean_inc(v_stx_1411_);
v___x_1415_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1409_, v_stx_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1468_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1468_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1468_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v_env_1421_; uint8_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1420_ = lean_st_ref_get(v___y_1413_);
v_env_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_ref(v_env_1421_);
lean_dec(v___x_1420_);
v___x_1422_ = 1;
lean_inc(v_a_1416_);
v___x_1423_ = l_Lean_Environment_contains(v_env_1421_, v_a_1416_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1425_; 
lean_dec(v_stx_1411_);
if (v_isShared_1419_ == 0)
{
v___x_1425_ = v___x_1418_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1416_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
uint8_t v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1418_);
v___x_1427_ = 0;
lean_inc(v_a_1416_);
v___x_1428_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1416_, v___x_1427_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1428_, 0);
lean_dec(v_unused_1459_);
v___x_1430_ = v___x_1428_;
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v___x_1428_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v_infoState_1433_; uint8_t v_enabled_1434_; 
v___x_1432_ = lean_st_ref_get(v___y_1413_);
v_infoState_1433_ = lean_ctor_get(v___x_1432_, 7);
lean_inc_ref(v_infoState_1433_);
lean_dec(v___x_1432_);
v_enabled_1434_ = lean_ctor_get_uint8(v_infoState_1433_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1433_);
if (v_enabled_1434_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_stx_1411_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_a_1416_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1416_);
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
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_del_object(v___x_1430_);
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = l_Lean_Syntax_getArg(v_stx_1411_, v___x_1438_);
lean_dec(v_stx_1411_);
v___x_1440_ = lean_box(0);
lean_inc(v_a_1416_);
v___x_1441_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1439_, v_a_1416_, v___x_1440_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1449_);
v___x_1443_ = v___x_1441_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1441_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_a_1416_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1416_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_a_1416_);
v_a_1450_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1441_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1441_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1416_);
lean_dec(v_stx_1411_);
v_a_1460_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1428_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1428_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1411_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1469_, lean_object* v_x_1470_, lean_object* v_stx_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v_x_7361__boxed_1475_; lean_object* v_res_1476_; 
v_x_7361__boxed_1475_ = lean_unbox(v_x_1470_);
v_res_1476_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1469_, v_x_7361__boxed_1475_, v_stx_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1479_, lean_object* v_attrName_1480_, lean_object* v_parserNamespace_1481_, lean_object* v_typeName_1482_, lean_object* v_kind_1483_, lean_object* v_attrDeclName_1484_){
_start:
{
lean_object* v___f_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___f_1486_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1487_, 0, v_parserNamespace_1481_);
v___x_1488_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1489_ = lean_string_append(v_kind_1483_, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1490_, 0, v_attrBuiltinName_1479_);
lean_ctor_set(v___x_1490_, 1, v_attrName_1480_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
lean_ctor_set(v___x_1490_, 3, v_typeName_1482_);
lean_ctor_set(v___x_1490_, 4, v___f_1487_);
lean_ctor_set(v___x_1490_, 5, v___f_1486_);
v___x_1491_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1490_, v_attrDeclName_1484_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1492_, lean_object* v_attrName_1493_, lean_object* v_parserNamespace_1494_, lean_object* v_typeName_1495_, lean_object* v_kind_1496_, lean_object* v_attrDeclName_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1492_, v_attrName_1493_, v_parserNamespace_1494_, v_typeName_1495_, v_kind_1496_, v_attrDeclName_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1500_, lean_object* v_attrBuiltinName_1501_, lean_object* v_attrName_1502_, lean_object* v_parserNamespace_1503_, lean_object* v_typeName_1504_, lean_object* v_kind_1505_, lean_object* v_attrDeclName_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1501_, v_attrName_1502_, v_parserNamespace_1503_, v_typeName_1504_, v_kind_1505_, v_attrDeclName_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1509_, lean_object* v_attrBuiltinName_1510_, lean_object* v_attrName_1511_, lean_object* v_parserNamespace_1512_, lean_object* v_typeName_1513_, lean_object* v_kind_1514_, lean_object* v_attrDeclName_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1509_, v_attrBuiltinName_1510_, v_attrName_1511_, v_parserNamespace_1512_, v_typeName_1513_, v_kind_1514_, v_attrDeclName_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1518_, lean_object* v_m_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1519_, v_a_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1522_, v_m_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_m_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1526_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
uint8_t v___x_1539_; 
v___x_1539_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1537_, v_x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_res_1543_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1540_, v_x_1541_, v_x_1542_);
lean_dec_ref(v_x_1542_);
lean_dec_ref(v_x_1541_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1545_, lean_object* v_a_1546_, lean_object* v_x_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1546_, v_x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_a_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1549_, v_a_1550_, v_x_1551_);
lean_dec(v_x_1551_);
lean_dec(v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1553_, lean_object* v_x_1554_, size_t v_x_1555_, lean_object* v_x_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1554_, v_x_1555_, v_x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
size_t v_x_7531__boxed_1562_; uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_x_7531__boxed_1562_ = lean_unbox_usize(v_x_1560_);
lean_dec(v_x_1560_);
v_res_1563_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1558_, v_x_1559_, v_x_7531__boxed_1562_, v_x_1561_);
lean_dec_ref(v_x_1561_);
lean_dec_ref(v_x_1559_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1565_, lean_object* v_constName_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1566_, v___y_1567_, v___y_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_constName_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1571_, v_constName_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1577_, lean_object* v_keys_1578_, lean_object* v_vals_1579_, lean_object* v_heq_1580_, lean_object* v_i_1581_, lean_object* v_k_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1578_, v_i_1581_, v_k_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1584_, lean_object* v_keys_1585_, lean_object* v_vals_1586_, lean_object* v_heq_1587_, lean_object* v_i_1588_, lean_object* v_k_1589_){
_start:
{
uint8_t v_res_1590_; lean_object* v_r_1591_; 
v_res_1590_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1584_, v_keys_1585_, v_vals_1586_, v_heq_1587_, v_i_1588_, v_k_1589_);
lean_dec_ref(v_k_1589_);
lean_dec_ref(v_vals_1586_);
lean_dec_ref(v_keys_1585_);
v_r_1591_ = lean_box(v_res_1590_);
return v_r_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1592_, lean_object* v_ref_1593_, lean_object* v_constName_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1593_, v_constName_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_ref_1600_, lean_object* v_constName_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1599_, v_ref_1600_, v_constName_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v_ref_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1606_, lean_object* v_ref_1607_, lean_object* v_msg_1608_, lean_object* v_declHint_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1607_, v_msg_1608_, v_declHint_1609_, v___y_1610_, v___y_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_ref_1615_, lean_object* v_msg_1616_, lean_object* v_declHint_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1614_, v_ref_1615_, v_msg_1616_, v_declHint_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v_ref_1615_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1622_, lean_object* v_declHint_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1622_, v_declHint_1623_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1628_, lean_object* v_declHint_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1628_, v_declHint_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1634_, lean_object* v_ref_1635_, lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1635_, v_msg_1636_, v___y_1637_, v___y_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1641_, lean_object* v_ref_1642_, lean_object* v_msg_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1641_, v_ref_1642_, v_msg_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_ref_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1661_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1662_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1663_ = lean_box(0);
v___x_1664_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1665_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1660_, v___x_1662_, v___x_1663_, v___x_1664_, v___x_1661_, v_ref_1658_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1676_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1682_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1683_ = l_Lean_addBuiltinDocString(v___x_1681_, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1713_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1714_ = l_Lean_addBuiltinDeclarationRanges(v___x_1712_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1717_, lean_object* v_a_1718_, lean_object* v_____r_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_declName_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
v_declName_1722_ = lean_ctor_get(v_toOLeanEntry_1717_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_toOLeanEntry_1717_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_toOLeanEntry_1717_, 0);
lean_dec(v_unused_1734_);
v___x_1724_ = v_toOLeanEntry_1717_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_declName_1722_);
lean_dec(v_toOLeanEntry_1717_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_a_1718_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1726_);
lean_ctor_set(v___x_1724_, 0, v_declName_1722_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_declName_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___y_1721_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1735_, lean_object* v_a_1736_, lean_object* v_____r_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1735_, v_a_1736_, v_____r_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1744_, lean_object* v_as_x27_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
if (lean_obj_tag(v_as_x27_1745_) == 0)
{
lean_object* v___x_1749_; 
lean_dec(v_stx_1744_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_b_1746_);
lean_ctor_set(v___x_1749_, 1, v___y_1748_);
return v___x_1749_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v_b_1746_);
v_head_1750_ = lean_ctor_get(v_as_x27_1745_, 0);
v_tail_1751_ = lean_ctor_get(v_as_x27_1745_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_as_x27_1745_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1753_ = v_as_x27_1745_;
v_isShared_1754_ = v_isSharedCheck_1829_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_as_x27_1745_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1829_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_toOLeanEntry_1755_; uint8_t v_isBuiltin_1756_; lean_object* v_value_1757_; lean_object* v_macroScope_1758_; lean_object* v_traceMsgs_1759_; lean_object* v_expandedMacroDecls_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1828_; 
v_toOLeanEntry_1755_ = lean_ctor_get(v_head_1750_, 0);
lean_inc_ref(v_toOLeanEntry_1755_);
v_isBuiltin_1756_ = lean_ctor_get_uint8(v_head_1750_, sizeof(void*)*2);
v_value_1757_ = lean_ctor_get(v_head_1750_, 1);
lean_inc(v_value_1757_);
lean_dec(v_head_1750_);
v_macroScope_1758_ = lean_ctor_get(v___y_1748_, 0);
v_traceMsgs_1759_ = lean_ctor_get(v___y_1748_, 1);
v_expandedMacroDecls_1760_ = lean_ctor_get(v___y_1748_, 2);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1762_ = v___y_1748_;
v_isShared_1763_ = v_isSharedCheck_1828_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_expandedMacroDecls_1760_);
lean_inc(v_traceMsgs_1759_);
lean_inc(v_macroScope_1758_);
lean_dec(v___y_1748_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1828_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_methods_1764_; lean_object* v_quotContext_1765_; lean_object* v_currRecDepth_1766_; lean_object* v_maxRecDepth_1767_; lean_object* v_ref_1768_; lean_object* v___x_1769_; lean_object* v_a_1771_; lean_object* v_a_1772_; lean_object* v___x_1776_; lean_object* v_a_1778_; lean_object* v_a_1779_; lean_object* v___y_1793_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v_methods_1764_ = lean_ctor_get(v___y_1747_, 0);
v_quotContext_1765_ = lean_ctor_get(v___y_1747_, 1);
v_currRecDepth_1766_ = lean_ctor_get(v___y_1747_, 3);
v_maxRecDepth_1767_ = lean_ctor_get(v___y_1747_, 4);
v_ref_1768_ = lean_ctor_get(v___y_1747_, 5);
v___x_1769_ = lean_box(0);
v___x_1776_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_nat_add(v_macroScope_1758_, v___x_1799_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1800_);
v___x_1802_ = v___x_1762_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_traceMsgs_1759_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_expandedMacroDecls_1760_);
v___x_1802_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1801_;
}
v___jp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_a_1771_);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v___x_1769_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v_a_1772_);
return v___x_1775_;
}
v___jp_1777_:
{
if (lean_obj_tag(v_a_1778_) == 1)
{
lean_dec_ref(v_toOLeanEntry_1755_);
v_as_x27_1745_ = v_tail_1751_;
v_b_1746_ = v___x_1776_;
v___y_1748_ = v_a_1779_;
goto _start;
}
else
{
lean_object* v_declName_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_tail_1751_);
lean_dec(v_stx_1744_);
v_declName_1781_ = lean_ctor_get(v_toOLeanEntry_1755_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_toOLeanEntry_1755_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_toOLeanEntry_1755_, 0);
lean_dec(v_unused_1791_);
v___x_1783_ = v_toOLeanEntry_1755_;
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_declName_1781_);
lean_dec(v_toOLeanEntry_1755_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_a_1778_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v___x_1785_);
lean_ctor_set(v___x_1783_, 0, v_declName_1781_);
v___x_1787_ = v___x_1783_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_declName_1781_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
v_a_1771_ = v___x_1788_;
v_a_1772_ = v_a_1779_;
goto v___jp_1770_;
}
}
}
}
v___jp_1792_:
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___y_1793_, 0);
if (lean_obj_tag(v_a_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v_a_1796_; 
lean_inc_ref(v_a_1794_);
lean_dec(v_tail_1751_);
lean_dec(v_stx_1744_);
v_a_1795_ = lean_ctor_get(v___y_1793_, 1);
lean_inc(v_a_1795_);
lean_dec_ref(v___y_1793_);
v_a_1796_ = lean_ctor_get(v_a_1794_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v_a_1794_);
v_a_1771_ = v_a_1796_;
v_a_1772_ = v_a_1795_;
goto v___jp_1770_;
}
else
{
lean_object* v_a_1797_; 
v_a_1797_ = lean_ctor_get(v___y_1793_, 1);
lean_inc(v_a_1797_);
lean_dec_ref(v___y_1793_);
v_as_x27_1745_ = v_tail_1751_;
v_b_1746_ = v___x_1776_;
v___y_1748_ = v_a_1797_;
goto _start;
}
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_inc(v_ref_1768_);
lean_inc(v_maxRecDepth_1767_);
lean_inc(v_currRecDepth_1766_);
lean_inc(v_quotContext_1765_);
lean_inc(v_methods_1764_);
v___x_1803_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1803_, 0, v_methods_1764_);
lean_ctor_set(v___x_1803_, 1, v_quotContext_1765_);
lean_ctor_set(v___x_1803_, 2, v_macroScope_1758_);
lean_ctor_set(v___x_1803_, 3, v_currRecDepth_1766_);
lean_ctor_set(v___x_1803_, 4, v_maxRecDepth_1767_);
lean_ctor_set(v___x_1803_, 5, v_ref_1768_);
lean_inc(v_stx_1744_);
v___x_1804_ = lean_apply_3(v_value_1757_, v_stx_1744_, v___x_1803_, v___x_1802_);
if (lean_obj_tag(v___x_1804_) == 0)
{
if (v_isBuiltin_1756_ == 0)
{
lean_object* v_a_1805_; lean_object* v_a_1806_; lean_object* v_macroScope_1807_; lean_object* v_traceMsgs_1808_; lean_object* v_expandedMacroDecls_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1821_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_a_1805_);
v_a_1806_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1804_);
v_macroScope_1807_ = lean_ctor_get(v_a_1805_, 0);
v_traceMsgs_1808_ = lean_ctor_get(v_a_1805_, 1);
v_expandedMacroDecls_1809_ = lean_ctor_get(v_a_1805_, 2);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_a_1805_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1811_ = v_a_1805_;
v_isShared_1812_ = v_isSharedCheck_1821_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_expandedMacroDecls_1809_);
lean_inc(v_traceMsgs_1808_);
lean_inc(v_macroScope_1807_);
lean_dec(v_a_1805_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1821_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_declName_1813_; lean_object* v___x_1815_; 
v_declName_1813_ = lean_ctor_get(v_toOLeanEntry_1755_, 1);
lean_inc(v_declName_1813_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v_expandedMacroDecls_1809_);
lean_ctor_set(v___x_1753_, 0, v_declName_1813_);
v___x_1815_ = v___x_1753_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_declName_1813_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_expandedMacroDecls_1809_);
v___x_1815_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 2, v___x_1815_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_macroScope_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_traceMsgs_1808_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1755_, v_a_1806_, v___x_1769_, v___y_1747_, v___x_1817_);
v___y_1793_ = v___x_1818_;
goto v___jp_1792_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v_a_1823_; lean_object* v___x_1824_; 
lean_del_object(v___x_1753_);
v_a_1822_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1822_);
v_a_1823_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1804_);
v___x_1824_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1755_, v_a_1822_, v___x_1769_, v___y_1747_, v_a_1823_);
v___y_1793_ = v___x_1824_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1825_; lean_object* v_a_1826_; 
lean_del_object(v___x_1753_);
v_a_1825_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1825_);
v_a_1826_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1804_);
v_a_1778_ = v_a_1825_;
v_a_1779_ = v_a_1826_;
goto v___jp_1777_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1830_, lean_object* v_as_x27_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1830_, v_as_x27_1831_, v_b_1832_, v___y_1833_, v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1836_, lean_object* v_stx_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v_fst_1847_; 
v___x_1840_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1837_);
v___x_1841_ = l_Lean_Syntax_getKind(v_stx_1837_);
v___x_1842_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1840_, v_env_1836_, v___x_1841_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v___x_1844_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1845_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1837_, v___x_1842_, v___x_1844_, v_a_1838_, v_a_1839_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
v_fst_1847_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_fst_1847_);
lean_dec(v_a_1846_);
if (lean_obj_tag(v_fst_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
v_a_1848_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1856_);
v___x_1850_ = v___x_1845_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1845_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1843_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_a_1857_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1866_);
v___x_1859_ = v___x_1845_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1845_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_val_1861_; lean_object* v___x_1863_; 
v_val_1861_ = lean_ctor_get(v_fst_1847_, 0);
lean_inc(v_val_1861_);
lean_dec_ref(v_fst_1847_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_val_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_val_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1857_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1867_, lean_object* v_stx_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1867_, v_stx_1868_, v_a_1869_, v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1872_, lean_object* v_as_1873_, lean_object* v_as_x27_1874_, lean_object* v_b_1875_, lean_object* v_a_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1872_, v_as_x27_1874_, v_b_1875_, v___y_1877_, v___y_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1880_, lean_object* v_as_1881_, lean_object* v_as_x27_1882_, lean_object* v_b_1883_, lean_object* v_a_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1880_, v_as_1881_, v_as_x27_1882_, v_b_1883_, v_a_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v_as_1881_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1888_, lean_object* v_inst_1889_, lean_object* v_s_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_apply_1(v_setNextMacroScope_1888_, v_s_1890_);
v___x_1892_ = lean_apply_2(v_inst_1889_, lean_box(0), v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1908_, lean_object* v_n_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_){
_start:
{
lean_object* v_getNextMacroScope_1913_; lean_object* v_setNextMacroScope_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
v_getNextMacroScope_1913_ = lean_ctor_get(v_inst_1912_, 1);
v_setNextMacroScope_1914_ = lean_ctor_get(v_inst_1912_, 2);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_inst_1912_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v_inst_1912_, 0);
lean_dec(v_unused_1924_);
v___x_1916_ = v_inst_1912_;
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_setNextMacroScope_1914_);
lean_inc(v_getNextMacroScope_1913_);
lean_dec(v_inst_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_inc(v_inst_1910_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1918_, 0, v_setNextMacroScope_1914_);
lean_closure_set(v___f_1918_, 1, v_inst_1910_);
v___x_1919_ = lean_apply_2(v_inst_1910_, lean_box(0), v_getNextMacroScope_1913_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 2, v___f_1918_);
lean_ctor_set(v___x_1916_, 1, v___x_1919_);
lean_ctor_set(v___x_1916_, 0, v_inst_1911_);
v___x_1921_ = v___x_1916_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_inst_1911_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v___f_1918_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1925_, lean_object* v_snd_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_toMonadRef_1929_, lean_object* v_inst_1930_, lean_object* v_fst_1931_, uint8_t v_____do__lift_1932_){
_start:
{
if (v_____do__lift_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec(v_fst_1931_);
lean_dec(v_inst_1930_);
lean_dec_ref(v_toMonadRef_1929_);
lean_dec_ref(v_inst_1928_);
lean_dec_ref(v_inst_1927_);
lean_dec_ref(v_snd_1926_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_apply_2(v_toPure_1925_, lean_box(0), v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_toPure_1925_);
v___x_1935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_snd_1926_);
v___x_1936_ = l_Lean_MessageData_ofFormat(v___x_1935_);
v___x_1937_ = l_Lean_addTrace___redArg(v_inst_1927_, v_inst_1928_, v_toMonadRef_1929_, v_inst_1930_, v_fst_1931_, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1938_, lean_object* v_snd_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_toMonadRef_1942_, lean_object* v_inst_1943_, lean_object* v_fst_1944_, lean_object* v_____do__lift_1945_){
_start:
{
uint8_t v_____do__lift_1416__boxed_1946_; lean_object* v_res_1947_; 
v_____do__lift_1416__boxed_1946_ = lean_unbox(v_____do__lift_1945_);
v_res_1947_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1938_, v_snd_1939_, v_inst_1940_, v_inst_1941_, v_toMonadRef_1942_, v_inst_1943_, v_fst_1944_, v_____do__lift_1416__boxed_1946_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1948_, lean_object* v_fst_1949_, lean_object* v_____do__lift_1950_, lean_object* v_____do__lift_1951_){
_start:
{
uint8_t v_hasTrace_1952_; 
v_hasTrace_1952_ = lean_ctor_get_uint8(v_____do__lift_1951_, sizeof(void*)*1);
if (v_hasTrace_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v_fst_1949_);
v___x_1953_ = lean_box(v_hasTrace_1952_);
v___x_1954_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14));
v___x_1956_ = l_Lean_Name_append(v___x_1955_, v_fst_1949_);
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1950_, v_____do__lift_1951_, v___x_1956_);
lean_dec(v___x_1956_);
v___x_1958_ = lean_box(v___x_1957_);
v___x_1959_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1958_);
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(lean_object* v_toPure_1960_, lean_object* v_fst_1961_, lean_object* v_____do__lift_1962_, lean_object* v_____do__lift_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Elab_liftMacroM___redArg___lam__1(v_toPure_1960_, v_fst_1961_, v_____do__lift_1962_, v_____do__lift_1963_);
lean_dec_ref(v_____do__lift_1963_);
lean_dec_ref(v_____do__lift_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1965_, lean_object* v_fst_1966_, lean_object* v_toBind_1967_, lean_object* v_inst_1968_, lean_object* v_____do__lift_1969_){
_start:
{
lean_object* v___f_1970_; lean_object* v___x_1971_; 
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1970_, 0, v_toPure_1965_);
lean_closure_set(v___f_1970_, 1, v_fst_1966_);
lean_closure_set(v___f_1970_, 2, v_____do__lift_1969_);
v___x_1971_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v_inst_1968_, v___f_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1972_, lean_object* v_toPure_1973_, lean_object* v_inst_1974_, lean_object* v_toMonadRef_1975_, lean_object* v_inst_1976_, lean_object* v_toBind_1977_, lean_object* v_inst_1978_, lean_object* v_x_1979_){
_start:
{
lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v_getInheritedTraceOptions_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_fst_1980_ = lean_ctor_get(v_x_1979_, 0);
lean_inc_n(v_fst_1980_, 2);
v_snd_1981_ = lean_ctor_get(v_x_1979_, 1);
lean_inc(v_snd_1981_);
lean_dec_ref(v_x_1979_);
v_getInheritedTraceOptions_1982_ = lean_ctor_get(v_inst_1972_, 2);
lean_inc(v_getInheritedTraceOptions_1982_);
lean_inc(v_toPure_1973_);
v___f_1983_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1983_, 0, v_toPure_1973_);
lean_closure_set(v___f_1983_, 1, v_snd_1981_);
lean_closure_set(v___f_1983_, 2, v_inst_1974_);
lean_closure_set(v___f_1983_, 3, v_inst_1972_);
lean_closure_set(v___f_1983_, 4, v_toMonadRef_1975_);
lean_closure_set(v___f_1983_, 5, v_inst_1976_);
lean_closure_set(v___f_1983_, 6, v_fst_1980_);
lean_inc_n(v_toBind_1977_, 2);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1984_, 0, v_toPure_1973_);
lean_closure_set(v___f_1984_, 1, v_fst_1980_);
lean_closure_set(v___f_1984_, 2, v_toBind_1977_);
lean_closure_set(v___f_1984_, 3, v_inst_1978_);
v___x_1985_ = lean_apply_4(v_toBind_1977_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1982_, v___f_1984_);
v___x_1986_ = lean_apply_4(v_toBind_1977_, lean_box(0), lean_box(0), v___x_1985_, v___f_1983_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v_stx_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
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
lean_object* v___x_1195__overap_2017_; lean_object* v___x_2018_; 
v___x_1195__overap_2017_ = l_liftExcept___redArg(v___x_1988_, v___x_1989_, v___x_2016_);
lean_inc_ref(v___y_1991_);
v___x_2018_ = lean_apply_2(v___x_1195__overap_2017_, v___y_1991_, v_a_2010_);
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
lean_object* v___x_1199__overap_2030_; lean_object* v___x_2031_; 
v___x_1199__overap_2030_ = l_liftExcept___redArg(v___x_1988_, v___x_1989_, v___x_2029_);
lean_inc_ref(v___y_1991_);
v___x_2031_ = lean_apply_2(v___x_1199__overap_2030_, v___y_1991_, v_a_2021_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2045_, lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v_stx_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2045_, v___x_2046_, v___x_2047_, v_stx_2048_, v___y_2049_, v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2052_, lean_object* v_declName_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2067_, lean_object* v_declName_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2067_, v_declName_2068_, v___y_2069_, v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2072_, lean_object* v_currNamespace_2073_, lean_object* v_openDecls_2074_, lean_object* v_n_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2080_, lean_object* v_currNamespace_2081_, lean_object* v_openDecls_2082_, lean_object* v_n_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2080_, v_currNamespace_2081_, v_openDecls_2082_, v_n_2083_, v___y_2084_, v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2087_, lean_object* v_opts_2088_, lean_object* v_currNamespace_2089_, lean_object* v_openDecls_2090_, lean_object* v_n_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2096_, lean_object* v_opts_2097_, lean_object* v_currNamespace_2098_, lean_object* v_openDecls_2099_, lean_object* v_n_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2096_, v_opts_2097_, v_currNamespace_2098_, v_openDecls_2099_, v_n_2100_, v___y_2101_, v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_opts_2097_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2104_, lean_object* v_a_2105_, lean_object* v_____r_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_apply_2(v_toPure_2104_, lean_box(0), v_a_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2108_, lean_object* v_inst_2109_, lean_object* v___f_2110_, lean_object* v_toBind_2111_, lean_object* v___f_2112_, lean_object* v_____r_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = l_List_reverse___redArg(v_traceMsgs_2108_);
v___x_2115_ = l_List_forM___redArg(v_inst_2109_, v___x_2114_, v___f_2110_);
v___x_2116_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2115_, v___f_2112_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2117_, lean_object* v_macroScope_2118_, lean_object* v_toBind_2119_, lean_object* v___f_2120_, lean_object* v_____s_2121_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_apply_1(v_setNextMacroScope_2117_, v_macroScope_2118_);
v___x_2123_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2122_, v___f_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2124_, lean_object* v_toPure_2125_, lean_object* v_____r_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2124_);
v___x_2128_ = lean_apply_2(v_toPure_2125_, lean_box(0), v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_toMonadRef_2133_, lean_object* v_inst_2134_, lean_object* v_toBind_2135_, lean_object* v___f_2136_, lean_object* v_a_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = 1;
v___x_2141_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2129_, v_inst_2130_, v_inst_2131_, v_inst_2132_, v_toMonadRef_2133_, v_inst_2134_, v_a_2137_, v___x_2140_);
v___x_2142_ = lean_apply_4(v_toBind_2135_, lean_box(0), lean_box(0), v___x_2141_, v___f_2136_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2144_, lean_object* v_____do__lift_2145_, lean_object* v_____do__lift_2146_, lean_object* v_____do__lift_2147_, lean_object* v_____do__lift_2148_, lean_object* v_____do__lift_2149_, lean_object* v_x_2150_, lean_object* v_toPure_2151_, lean_object* v_inst_2152_, lean_object* v___f_2153_, lean_object* v_toBind_2154_, lean_object* v_setNextMacroScope_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_toMonadRef_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_toMonadExceptOf_2162_, lean_object* v_____do__lift_2163_){
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
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2173_, 0, v_toPure_2151_);
lean_closure_set(v___f_2173_, 1, v_a_2169_);
lean_inc_n(v_toBind_2154_, 3);
lean_inc_ref_n(v_inst_2152_, 2);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2174_, 0, v_traceMsgs_2171_);
lean_closure_set(v___f_2174_, 1, v_inst_2152_);
lean_closure_set(v___f_2174_, 2, v___f_2153_);
lean_closure_set(v___f_2174_, 3, v_toBind_2154_);
lean_closure_set(v___f_2174_, 4, v___f_2173_);
v___f_2175_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2175_, 0, v_setNextMacroScope_2155_);
lean_closure_set(v___f_2175_, 1, v_macroScope_2170_);
lean_closure_set(v___f_2175_, 2, v_toBind_2154_);
lean_closure_set(v___f_2175_, 3, v___f_2174_);
v___x_2176_ = lean_box(0);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2177_, 0, v___x_2176_);
lean_closure_set(v___f_2177_, 1, v_toPure_2151_);
v___f_2178_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
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
v___x_2184_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
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
v_res_2211_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2191_, v_____do__lift_2192_, v_____do__lift_2193_, v_____do__lift_2194_, v_____do__lift_2195_, v_____do__lift_2196_, v_x_2197_, v_toPure_2198_, v_inst_2199_, v___f_2200_, v_toBind_2201_, v_setNextMacroScope_2202_, v_inst_2203_, v_inst_2204_, v_inst_2205_, v_toMonadRef_2206_, v_inst_2207_, v_inst_2208_, v_toMonadExceptOf_2209_, v_____do__lift_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2212_, lean_object* v_____do__lift_2213_, lean_object* v_____do__lift_2214_, lean_object* v_____do__lift_2215_, lean_object* v_____do__lift_2216_, lean_object* v_x_2217_, lean_object* v_toPure_2218_, lean_object* v_inst_2219_, lean_object* v___f_2220_, lean_object* v_toBind_2221_, lean_object* v_setNextMacroScope_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_toMonadRef_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_toMonadExceptOf_2229_, lean_object* v_getNextMacroScope_2230_, lean_object* v_____do__lift_2231_){
_start:
{
lean_object* v___f_2232_; lean_object* v___x_2233_; 
lean_inc(v_toBind_2221_);
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
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
v_res_2254_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2234_, v_____do__lift_2235_, v_____do__lift_2236_, v_____do__lift_2237_, v_____do__lift_2238_, v_x_2239_, v_toPure_2240_, v_inst_2241_, v___f_2242_, v_toBind_2243_, v_setNextMacroScope_2244_, v_inst_2245_, v_inst_2246_, v_inst_2247_, v_toMonadRef_2248_, v_inst_2249_, v_inst_2250_, v_toMonadExceptOf_2251_, v_getNextMacroScope_2252_, v_____do__lift_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2255_, lean_object* v_____do__lift_2256_, lean_object* v_____do__lift_2257_, lean_object* v_____do__lift_2258_, lean_object* v_x_2259_, lean_object* v_toPure_2260_, lean_object* v_inst_2261_, lean_object* v___f_2262_, lean_object* v_toBind_2263_, lean_object* v_setNextMacroScope_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_toMonadRef_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_toMonadExceptOf_2271_, lean_object* v_getNextMacroScope_2272_, lean_object* v_getMaxRecDepth_2273_, lean_object* v_____do__lift_2274_){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
lean_inc(v_toBind_2263_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
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
v_res_2297_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2277_, v_____do__lift_2278_, v_____do__lift_2279_, v_____do__lift_2280_, v_x_2281_, v_toPure_2282_, v_inst_2283_, v___f_2284_, v_toBind_2285_, v_setNextMacroScope_2286_, v_inst_2287_, v_inst_2288_, v_inst_2289_, v_toMonadRef_2290_, v_inst_2291_, v_inst_2292_, v_toMonadExceptOf_2293_, v_getNextMacroScope_2294_, v_getMaxRecDepth_2295_, v_____do__lift_2296_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2298_, lean_object* v_methods_2299_, lean_object* v_____do__lift_2300_, lean_object* v_____do__lift_2301_, lean_object* v_x_2302_, lean_object* v_toPure_2303_, lean_object* v_inst_2304_, lean_object* v___f_2305_, lean_object* v_toBind_2306_, lean_object* v_setNextMacroScope_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_toMonadRef_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_toMonadExceptOf_2314_, lean_object* v_getNextMacroScope_2315_, lean_object* v_____do__lift_2316_){
_start:
{
lean_object* v_getRecDepth_2317_; lean_object* v_getMaxRecDepth_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_getRecDepth_2317_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc(v_getRecDepth_2317_);
v_getMaxRecDepth_2318_ = lean_ctor_get(v_inst_2298_, 2);
lean_inc(v_getMaxRecDepth_2318_);
lean_dec_ref(v_inst_2298_);
lean_inc(v_toBind_2306_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
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
v_res_2340_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2321_, v_methods_2322_, v_____do__lift_2323_, v_____do__lift_2324_, v_x_2325_, v_toPure_2326_, v_inst_2327_, v___f_2328_, v_toBind_2329_, v_setNextMacroScope_2330_, v_inst_2331_, v_inst_2332_, v_inst_2333_, v_toMonadRef_2334_, v_inst_2335_, v_inst_2336_, v_toMonadExceptOf_2337_, v_getNextMacroScope_2338_, v_____do__lift_2339_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2341_, lean_object* v_methods_2342_, lean_object* v_____do__lift_2343_, lean_object* v_x_2344_, lean_object* v_toPure_2345_, lean_object* v_inst_2346_, lean_object* v___f_2347_, lean_object* v_toBind_2348_, lean_object* v_setNextMacroScope_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_toMonadRef_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_toMonadExceptOf_2356_, lean_object* v_getNextMacroScope_2357_, lean_object* v_getContext_2358_, lean_object* v_____do__lift_2359_){
_start:
{
lean_object* v___f_2360_; lean_object* v___x_2361_; 
lean_inc(v_toBind_2348_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
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
v_res_2381_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2362_, v_methods_2363_, v_____do__lift_2364_, v_x_2365_, v_toPure_2366_, v_inst_2367_, v___f_2368_, v_toBind_2369_, v_setNextMacroScope_2370_, v_inst_2371_, v_inst_2372_, v_inst_2373_, v_toMonadRef_2374_, v_inst_2375_, v_inst_2376_, v_toMonadExceptOf_2377_, v_getNextMacroScope_2378_, v_getContext_2379_, v_____do__lift_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2382_, lean_object* v_inst_2383_, lean_object* v_methods_2384_, lean_object* v_x_2385_, lean_object* v_toPure_2386_, lean_object* v_inst_2387_, lean_object* v___f_2388_, lean_object* v_toBind_2389_, lean_object* v_setNextMacroScope_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_toMonadRef_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_toMonadExceptOf_2397_, lean_object* v_getNextMacroScope_2398_, lean_object* v_____do__lift_2399_){
_start:
{
lean_object* v_getCurrMacroScope_2400_; lean_object* v_getContext_2401_; lean_object* v___f_2402_; lean_object* v___x_2403_; 
v_getCurrMacroScope_2400_ = lean_ctor_get(v_toMonadQuotation_2382_, 1);
lean_inc(v_getCurrMacroScope_2400_);
v_getContext_2401_ = lean_ctor_get(v_toMonadQuotation_2382_, 2);
lean_inc(v_getContext_2401_);
lean_dec_ref(v_toMonadQuotation_2382_);
lean_inc(v_toBind_2389_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
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
v_res_2422_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2404_, v_inst_2405_, v_methods_2406_, v_x_2407_, v_toPure_2408_, v_inst_2409_, v___f_2410_, v_toBind_2411_, v_setNextMacroScope_2412_, v_inst_2413_, v_inst_2414_, v_inst_2415_, v_toMonadRef_2416_, v_inst_2417_, v_inst_2418_, v_toMonadExceptOf_2419_, v_getNextMacroScope_2420_, v_____do__lift_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2423_, lean_object* v_env_2424_, lean_object* v_currNamespace_2425_, lean_object* v_opts_2426_, lean_object* v___x_2427_, lean_object* v___f_2428_, lean_object* v___f_2429_, lean_object* v_toMonadQuotation_2430_, lean_object* v_inst_2431_, lean_object* v_x_2432_, lean_object* v_toPure_2433_, lean_object* v_inst_2434_, lean_object* v___f_2435_, lean_object* v_toBind_2436_, lean_object* v_setNextMacroScope_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_toMonadExceptOf_2443_, lean_object* v_getNextMacroScope_2444_, lean_object* v_openDecls_2445_){
_start:
{
lean_object* v_getRef_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; lean_object* v_methods_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v_getRef_2446_ = lean_ctor_get(v_toMonadRef_2423_, 0);
lean_inc(v_getRef_2446_);
lean_inc(v_openDecls_2445_);
lean_inc_n(v_currNamespace_2425_, 2);
lean_inc_ref(v_env_2424_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2447_, 0, v_env_2424_);
lean_closure_set(v___f_2447_, 1, v_currNamespace_2425_);
lean_closure_set(v___f_2447_, 2, v_openDecls_2445_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
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
v___f_2451_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
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
v_res_2476_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2453_, v_env_2454_, v_currNamespace_2455_, v_opts_2456_, v___x_2457_, v___f_2458_, v___f_2459_, v_toMonadQuotation_2460_, v_inst_2461_, v_x_2462_, v_toPure_2463_, v_inst_2464_, v___f_2465_, v_toBind_2466_, v_setNextMacroScope_2467_, v_inst_2468_, v_inst_2469_, v_inst_2470_, v_inst_2471_, v_inst_2472_, v_toMonadExceptOf_2473_, v_getNextMacroScope_2474_, v_openDecls_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2477_, lean_object* v_env_2478_, lean_object* v_opts_2479_, lean_object* v___x_2480_, lean_object* v___f_2481_, lean_object* v___f_2482_, lean_object* v_toMonadQuotation_2483_, lean_object* v_inst_2484_, lean_object* v_x_2485_, lean_object* v_toPure_2486_, lean_object* v_inst_2487_, lean_object* v___f_2488_, lean_object* v_toBind_2489_, lean_object* v_setNextMacroScope_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_toMonadExceptOf_2496_, lean_object* v_getNextMacroScope_2497_, lean_object* v_getOpenDecls_2498_, lean_object* v_currNamespace_2499_){
_start:
{
lean_object* v___f_2500_; lean_object* v___x_2501_; 
lean_inc(v_toBind_2489_);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
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
v_res_2525_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2502_, v_env_2503_, v_opts_2504_, v___x_2505_, v___f_2506_, v___f_2507_, v_toMonadQuotation_2508_, v_inst_2509_, v_x_2510_, v_toPure_2511_, v_inst_2512_, v___f_2513_, v_toBind_2514_, v_setNextMacroScope_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_inst_2519_, v_inst_2520_, v_toMonadExceptOf_2521_, v_getNextMacroScope_2522_, v_getOpenDecls_2523_, v_currNamespace_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2526_, lean_object* v_toMonadRef_2527_, lean_object* v_env_2528_, lean_object* v___x_2529_, lean_object* v___f_2530_, lean_object* v___f_2531_, lean_object* v_toMonadQuotation_2532_, lean_object* v_inst_2533_, lean_object* v_x_2534_, lean_object* v_toPure_2535_, lean_object* v_inst_2536_, lean_object* v___f_2537_, lean_object* v_toBind_2538_, lean_object* v_setNextMacroScope_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_toMonadExceptOf_2545_, lean_object* v_getNextMacroScope_2546_, lean_object* v_opts_2547_){
_start:
{
lean_object* v_getCurrNamespace_2548_; lean_object* v_getOpenDecls_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; 
v_getCurrNamespace_2548_ = lean_ctor_get(v_inst_2526_, 0);
lean_inc(v_getCurrNamespace_2548_);
v_getOpenDecls_2549_ = lean_ctor_get(v_inst_2526_, 1);
lean_inc(v_getOpenDecls_2549_);
lean_dec_ref(v_inst_2526_);
lean_inc(v_toBind_2538_);
v___f_2550_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
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
v_res_2574_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2552_, v_toMonadRef_2553_, v_env_2554_, v___x_2555_, v___f_2556_, v___f_2557_, v_toMonadQuotation_2558_, v_inst_2559_, v_x_2560_, v_toPure_2561_, v_inst_2562_, v___f_2563_, v_toBind_2564_, v_setNextMacroScope_2565_, v_inst_2566_, v_inst_2567_, v_inst_2568_, v_inst_2569_, v_inst_2570_, v_toMonadExceptOf_2571_, v_getNextMacroScope_2572_, v_opts_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_inst_2577_, lean_object* v_toMonadRef_2578_, lean_object* v___x_2579_, lean_object* v_toMonadQuotation_2580_, lean_object* v_inst_2581_, lean_object* v_x_2582_, lean_object* v_toPure_2583_, lean_object* v_inst_2584_, lean_object* v___f_2585_, lean_object* v_toBind_2586_, lean_object* v_setNextMacroScope_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_toMonadExceptOf_2593_, lean_object* v_getNextMacroScope_2594_, lean_object* v_env_2595_){
_start:
{
lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; 
lean_inc_ref_n(v_env_2595_, 2);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2596_, 0, v_env_2595_);
lean_closure_set(v___f_2596_, 1, v___x_2575_);
lean_closure_set(v___f_2596_, 2, v___x_2576_);
v___f_2597_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2597_, 0, v_env_2595_);
lean_inc(v_inst_2590_);
lean_inc(v_toBind_2586_);
v___f_2598_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
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
v_res_2621_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v___x_2600_, v___x_2601_, v_inst_2602_, v_toMonadRef_2603_, v___x_2604_, v_toMonadQuotation_2605_, v_inst_2606_, v_x_2607_, v_toPure_2608_, v_inst_2609_, v___f_2610_, v_toBind_2611_, v_setNextMacroScope_2612_, v_inst_2613_, v_inst_2614_, v_inst_2615_, v_inst_2616_, v_inst_2617_, v_toMonadExceptOf_2618_, v_getNextMacroScope_2619_, v_env_2620_);
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
lean_inc_n(v_toBind_2666_, 3);
v_getEnv_2667_ = lean_ctor_get(v_inst_2655_, 0);
lean_inc(v_getEnv_2667_);
v_toMonadExceptOf_2668_ = lean_ctor_get(v_inst_2657_, 0);
lean_inc_ref(v_toMonadExceptOf_2668_);
v_toMonadRef_2669_ = lean_ctor_get(v_inst_2657_, 1);
lean_inc_ref_n(v_toMonadRef_2669_, 2);
v_toMonadQuotation_2670_ = lean_ctor_get(v_inst_2654_, 0);
lean_inc_ref(v_toMonadQuotation_2670_);
v_getNextMacroScope_2671_ = lean_ctor_get(v_inst_2654_, 1);
lean_inc(v_getNextMacroScope_2671_);
v_setNextMacroScope_2672_ = lean_ctor_get(v_inst_2654_, 2);
lean_inc(v_setNextMacroScope_2672_);
lean_dec_ref(v_inst_2654_);
v_toPure_2673_ = lean_ctor_get(v_toApplicative_2665_, 1);
lean_inc_n(v_toPure_2673_, 2);
v___x_2674_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2660_);
lean_inc(v_inst_2661_);
lean_inc_ref(v_inst_2653_);
lean_inc_ref(v_inst_2659_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2675_, 0, v_inst_2659_);
lean_closure_set(v___f_2675_, 1, v_toPure_2673_);
lean_closure_set(v___f_2675_, 2, v_inst_2653_);
lean_closure_set(v___f_2675_, 3, v_toMonadRef_2669_);
lean_closure_set(v___f_2675_, 4, v_inst_2661_);
lean_closure_set(v___f_2675_, 5, v_toBind_2666_);
lean_closure_set(v___f_2675_, 6, v_inst_2660_);
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
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
lean_inc_n(v_a_2790_, 2);
v_a_2791_ = lean_ctor_get(v___x_2789_, 1);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2789_);
lean_inc(v_baseName_2786_);
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
v___x_2913_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
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
lean_inc_n(v_toBind_2952_, 2);
v_toPure_2953_ = lean_ctor_get(v_toApplicative_2951_, 1);
lean_inc(v_toPure_2953_);
lean_inc_ref(v_inst_2949_);
v___x_2954_ = l_Lean_getRefPos___redArg(v_inst_2948_, v_inst_2949_);
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
lean_inc_ref_n(v_inst_2979_, 2);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2984_, 0, v_inst_2979_);
lean_closure_set(v___f_2984_, 1, v_inst_2980_);
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
