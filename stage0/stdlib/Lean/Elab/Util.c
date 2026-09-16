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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* v_val_94_; lean_object* v_val_95_; uint8_t v_decide_96_; 
v_val_94_ = lean_ctor_get(v_x_89_, 0);
v_val_95_ = lean_ctor_get(v_x_90_, 0);
v_decide_96_ = lean_nat_dec_eq(v_val_94_, v_val_95_);
return v_decide_96_;
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
lean_dec_ref_known(v___x_119_, 1);
v_before_121_ = lean_ctor_get(v_val_120_, 0);
lean_inc(v_before_121_);
lean_dec(v_val_120_);
return v_before_121_;
}
}
else
{
lean_dec_ref_known(v___x_118_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1(lean_object* v___x_213_, lean_object* v_toPure_214_, lean_object* v_msgData_215_, lean_object* v_macroStack_216_, lean_object* v_____do__lift_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = l_Lean_Elab_pp_macroStack;
v___x_219_ = l_Lean_Option_get___redArg(v___x_213_, v_____do__lift_217_, v___x_218_);
v___x_220_ = lean_unbox(v___x_219_);
lean_dec(v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_macroStack_216_);
v___x_221_ = lean_apply_2(v_toPure_214_, lean_box(0), v_msgData_215_);
return v___x_221_;
}
else
{
if (lean_obj_tag(v_macroStack_216_) == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_apply_2(v_toPure_214_, lean_box(0), v_msgData_215_);
return v___x_222_;
}
else
{
lean_object* v_head_223_; lean_object* v_after_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_240_; 
v_head_223_ = lean_ctor_get(v_macroStack_216_, 0);
lean_inc(v_head_223_);
v_after_224_ = lean_ctor_get(v_head_223_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_head_223_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_head_223_, 0);
lean_dec(v_unused_241_);
v___x_226_ = v_head_223_;
v_isShared_227_ = v_isSharedCheck_240_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_after_224_);
lean_dec(v_head_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_240_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___f_229_; lean_object* v___x_231_; 
v___x_228_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0);
v___f_229_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 7);
lean_ctor_set(v___x_226_, 1, v___x_228_);
lean_ctor_set(v___x_226_, 0, v_msgData_215_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_msgData_215_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_228_);
v___x_231_ = v_reuseFailAlloc_239_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_msgData_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_232_ = lean_obj_once(&l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4, &l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once, _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_MessageData_ofSyntax(v_after_224_);
v___x_235_ = l_Lean_indentD(v___x_234_);
v_msgData_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_236_, 0, v___x_233_);
lean_ctor_set(v_msgData_236_, 1, v___x_235_);
v___x_237_ = l_List_foldl___redArg(v___f_229_, v_msgData_236_, v_macroStack_216_);
v___x_238_ = lean_apply_2(v_toPure_214_, lean_box(0), v___x_237_);
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(lean_object* v___x_242_, lean_object* v_toPure_243_, lean_object* v_msgData_244_, lean_object* v_macroStack_245_, lean_object* v_____do__lift_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_addMacroStack___redArg___lam__1(v___x_242_, v_toPure_243_, v_msgData_244_, v_macroStack_245_, v_____do__lift_246_);
lean_dec_ref(v_____do__lift_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___redArg(lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_msgData_250_, lean_object* v_macroStack_251_){
_start:
{
lean_object* v___x_252_; lean_object* v_toApplicative_253_; lean_object* v_toBind_254_; lean_object* v_toPure_255_; lean_object* v___f_256_; lean_object* v___x_257_; 
v___x_252_ = l_Lean_KVMap_instValueBool;
v_toApplicative_253_ = lean_ctor_get(v_inst_248_, 0);
lean_inc_ref(v_toApplicative_253_);
v_toBind_254_ = lean_ctor_get(v_inst_248_, 1);
lean_inc(v_toBind_254_);
lean_dec_ref(v_inst_248_);
v_toPure_255_ = lean_ctor_get(v_toApplicative_253_, 1);
lean_inc(v_toPure_255_);
lean_dec_ref(v_toApplicative_253_);
v___f_256_ = lean_alloc_closure((void*)(l_Lean_Elab_addMacroStack___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_256_, 0, v___x_252_);
lean_closure_set(v___f_256_, 1, v_toPure_255_);
lean_closure_set(v___f_256_, 2, v_msgData_250_);
lean_closure_set(v___f_256_, 3, v_macroStack_251_);
v___x_257_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v_inst_249_, v___f_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack(lean_object* v_m_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_msgData_261_, lean_object* v_macroStack_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Elab_addMacroStack___redArg(v_inst_259_, v_inst_260_, v_msgData_261_, v_macroStack_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_____r_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_271_ = l_Lean_throwError___redArg(v_inst_267_, v_inst_268_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(lean_object* v_k_272_, lean_object* v___f_273_, lean_object* v_toPure_274_, lean_object* v_____do__lift_275_){
_start:
{
uint8_t v___x_276_; 
lean_inc(v_k_272_);
v___x_276_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_275_, v_k_272_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_toPure_274_);
lean_dec(v_k_272_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_apply_1(v___f_273_, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
lean_dec(v___f_273_);
v___x_279_ = lean_apply_2(v_toPure_274_, lean_box(0), v_k_272_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(lean_object* v_k_280_, lean_object* v___f_281_, lean_object* v_toPure_282_, lean_object* v_toBind_283_, lean_object* v_getEnv_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v_k_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_k_286_ = l_Lean_mkPrivateName(v_____do__lift_285_, v_k_280_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1), 4, 3);
lean_closure_set(v___f_287_, 0, v_k_286_);
lean_closure_set(v___f_287_, 1, v___f_281_);
lean_closure_set(v___f_287_, 2, v_toPure_282_);
v___x_288_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v_getEnv_284_, v___f_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(lean_object* v_k_289_, lean_object* v___f_290_, lean_object* v_toPure_291_, lean_object* v_toBind_292_, lean_object* v_getEnv_293_, lean_object* v_____do__lift_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(v_k_289_, v___f_290_, v_toPure_291_, v_toBind_292_, v_getEnv_293_, v_____do__lift_294_);
lean_dec_ref(v_____do__lift_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(lean_object* v___f_296_, lean_object* v_toBind_297_, lean_object* v_getEnv_298_, lean_object* v___f_299_, lean_object* v_k_300_, uint8_t v___x_301_, lean_object* v_____do__lift_302_){
_start:
{
uint8_t v_isExporting_310_; 
v_isExporting_310_ = lean_ctor_get_uint8(v_____do__lift_302_, sizeof(void*)*8);
if (v_isExporting_310_ == 0)
{
goto v___jp_306_;
}
else
{
if (v___x_301_ == 0)
{
lean_dec(v___f_299_);
lean_dec(v_getEnv_298_);
lean_dec(v_toBind_297_);
goto v___jp_303_;
}
else
{
goto v___jp_306_;
}
}
v___jp_303_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v___f_296_, v___x_304_);
return v___x_305_;
}
v___jp_306_:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_isPrivateName(v_k_300_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v___f_296_);
v___x_308_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v_getEnv_298_, v___f_299_);
return v___x_308_;
}
else
{
if (v___x_301_ == 0)
{
lean_dec(v___f_299_);
lean_dec(v_getEnv_298_);
lean_dec(v_toBind_297_);
goto v___jp_303_;
}
else
{
lean_object* v___x_309_; 
lean_dec(v___f_296_);
v___x_309_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v_getEnv_298_, v___f_299_);
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(lean_object* v___f_311_, lean_object* v_toBind_312_, lean_object* v_getEnv_313_, lean_object* v___f_314_, lean_object* v_k_315_, lean_object* v___x_316_, lean_object* v_____do__lift_317_){
_start:
{
uint8_t v___x_208__boxed_318_; lean_object* v_res_319_; 
v___x_208__boxed_318_ = lean_unbox(v___x_316_);
v_res_319_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(v___f_311_, v_toBind_312_, v_getEnv_313_, v___f_314_, v_k_315_, v___x_208__boxed_318_, v_____do__lift_317_);
lean_dec_ref(v_____do__lift_317_);
lean_dec(v_k_315_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(lean_object* v_k_320_, lean_object* v___f_321_, lean_object* v_toBind_322_, lean_object* v_getEnv_323_, lean_object* v___f_324_, lean_object* v_toPure_325_, lean_object* v_____do__lift_326_){
_start:
{
uint8_t v___x_327_; 
lean_inc(v_k_320_);
v___x_327_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_326_, v_k_320_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
lean_dec(v_toPure_325_);
v___x_328_ = lean_box(v___x_327_);
lean_inc(v_getEnv_323_);
lean_inc(v_toBind_322_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_329_, 0, v___f_321_);
lean_closure_set(v___f_329_, 1, v_toBind_322_);
lean_closure_set(v___f_329_, 2, v_getEnv_323_);
lean_closure_set(v___f_329_, 3, v___f_324_);
lean_closure_set(v___f_329_, 4, v_k_320_);
lean_closure_set(v___f_329_, 5, v___x_328_);
v___x_330_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_getEnv_323_, v___f_329_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
lean_dec(v___f_324_);
lean_dec(v_getEnv_323_);
lean_dec(v_toBind_322_);
lean_dec(v___f_321_);
v___x_331_ = lean_apply_2(v_toPure_325_, lean_box(0), v_k_320_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___redArg(lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_k_335_){
_start:
{
lean_object* v_toApplicative_336_; lean_object* v_toBind_337_; lean_object* v_getEnv_338_; lean_object* v_toPure_339_; lean_object* v___f_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v_toApplicative_336_ = lean_ctor_get(v_inst_332_, 0);
v_toBind_337_ = lean_ctor_get(v_inst_332_, 1);
lean_inc_n(v_toBind_337_, 3);
v_getEnv_338_ = lean_ctor_get(v_inst_333_, 0);
lean_inc_n(v_getEnv_338_, 3);
lean_dec_ref(v_inst_333_);
v_toPure_339_ = lean_ctor_get(v_toApplicative_336_, 1);
lean_inc_n(v_toPure_339_, 2);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0), 3, 2);
lean_closure_set(v___f_340_, 0, v_inst_332_);
lean_closure_set(v___f_340_, 1, v_inst_334_);
lean_inc_ref(v___f_340_);
lean_inc(v_k_335_);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_341_, 0, v_k_335_);
lean_closure_set(v___f_341_, 1, v___f_340_);
lean_closure_set(v___f_341_, 2, v_toPure_339_);
lean_closure_set(v___f_341_, 3, v_toBind_337_);
lean_closure_set(v___f_341_, 4, v_getEnv_338_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4), 7, 6);
lean_closure_set(v___f_342_, 0, v_k_335_);
lean_closure_set(v___f_342_, 1, v___f_340_);
lean_closure_set(v___f_342_, 2, v_toBind_337_);
lean_closure_set(v___f_342_, 3, v_getEnv_338_);
lean_closure_set(v___f_342_, 4, v___f_341_);
lean_closure_set(v___f_342_, 5, v_toPure_339_);
v___x_343_ = lean_apply_4(v_toBind_337_, lean_box(0), lean_box(0), v_getEnv_338_, v___f_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* v_m_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_345_, v_inst_346_, v_inst_347_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_k_353_, lean_object* v_pre_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(v_inst_350_, v_inst_351_, v_inst_352_, v_k_353_, v_pre_354_, v_x_355_);
lean_dec_ref(v_x_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_k_360_, lean_object* v_x_361_){
_start:
{
switch(lean_obj_tag(v_x_361_))
{
case 1:
{
lean_object* v_toMonadExceptOf_362_; lean_object* v_pre_363_; lean_object* v_tryCatch_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_toMonadExceptOf_362_ = lean_ctor_get(v_inst_359_, 0);
v_pre_363_ = lean_ctor_get(v_x_361_, 0);
v_tryCatch_364_ = lean_ctor_get(v_toMonadExceptOf_362_, 1);
lean_inc(v_tryCatch_364_);
lean_inc(v_pre_363_);
lean_inc(v_k_360_);
lean_inc_ref(v_inst_359_);
lean_inc_ref(v_inst_358_);
lean_inc_ref(v_inst_357_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_365_, 0, v_inst_357_);
lean_closure_set(v___f_365_, 1, v_inst_358_);
lean_closure_set(v___f_365_, 2, v_inst_359_);
lean_closure_set(v___f_365_, 3, v_k_360_);
lean_closure_set(v___f_365_, 4, v_pre_363_);
v___x_366_ = l_Lean_Name_append(v_x_361_, v_k_360_);
v___x_367_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_357_, v_inst_358_, v_inst_359_, v___x_366_);
v___x_368_ = lean_apply_3(v_tryCatch_364_, lean_box(0), v___x_367_, v___f_365_);
return v___x_368_;
}
case 0:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(v_inst_357_, v_inst_358_, v_inst_359_, v_k_360_);
return v___x_369_;
}
default: 
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_x_361_);
lean_dec(v_k_360_);
lean_dec_ref(v_inst_358_);
v___x_370_ = lean_obj_once(&l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1, &l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1);
v___x_371_ = l_Lean_throwError___redArg(v_inst_357_, v_inst_359_, v___x_370_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_k_375_, lean_object* v_pre_376_, lean_object* v_x_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_372_, v_inst_373_, v_inst_374_, v_k_375_, v_pre_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* v_m_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_k_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(v_inst_380_, v_inst_381_, v_inst_382_, v_k_383_, v_x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_386_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
lean_ctor_set(v___x_391_, 3, v___x_390_);
lean_ctor_set(v___x_391_, 4, v___x_389_);
lean_ctor_set(v___x_391_, 5, v___x_389_);
lean_ctor_set(v___x_391_, 6, v___x_389_);
lean_ctor_set(v___x_391_, 7, v___x_389_);
lean_ctor_set(v___x_391_, 8, v___x_389_);
lean_ctor_set(v___x_391_, 9, v___x_389_);
lean_ctor_set(v___x_391_, 10, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_unsigned_to_nat(32u);
v___x_393_ = lean_mk_empty_array_with_capacity(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((size_t)5ULL);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_unsigned_to_nat(32u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
v___x_400_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_396_);
lean_ctor_set(v___x_400_, 3, v___x_396_);
lean_ctor_set_usize(v___x_400_, 4, v___x_395_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_box(1);
v___x_402_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(lean_object* v_msgData_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_toCold_410_; lean_object* v_env_411_; lean_object* v_options_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_409_ = lean_st_ref_get(v___y_407_);
v_toCold_410_ = lean_ctor_get(v___y_406_, 0);
v_env_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_409_);
v_options_412_ = lean_ctor_get(v_toCold_410_, 2);
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
lean_ctor_set(v___x_416_, 1, v_msgData_405_);
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
v_ref_427_ = lean_ctor_get(v___y_424_, 2);
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
lean_object* v___x_455_; uint8_t v___y_457_; lean_object* v_env_474_; uint8_t v_isExporting_475_; 
v___x_455_ = lean_st_ref_get(v___y_445_);
v_env_474_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_474_);
lean_dec(v___x_455_);
v_isExporting_475_ = lean_ctor_get_uint8(v_env_474_, sizeof(void*)*8);
lean_dec_ref(v_env_474_);
if (v_isExporting_475_ == 0)
{
goto v___jp_465_;
}
else
{
if (v___x_454_ == 0)
{
v___y_457_ = v___x_454_;
goto v___jp_456_;
}
else
{
goto v___jp_465_;
}
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
lean_object* v___x_458_; lean_object* v_env_459_; lean_object* v_k_460_; lean_object* v___x_461_; lean_object* v_env_462_; uint8_t v___x_463_; 
v___x_458_ = lean_st_ref_get(v___y_445_);
v_env_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_459_);
lean_dec(v___x_458_);
v_k_460_ = l_Lean_mkPrivateName(v_env_459_, v_k_443_);
lean_dec_ref(v_env_459_);
v___x_461_ = lean_st_ref_get(v___y_445_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
lean_inc(v_k_460_);
v___x_463_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_462_, v_k_460_);
if (v___x_463_ == 0)
{
lean_dec(v_k_460_);
v___y_448_ = v___y_444_;
v___y_449_ = v___y_445_;
goto v___jp_447_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_k_460_);
return v___x_464_;
}
}
}
v___jp_465_:
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_isPrivateName(v_k_443_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v_k_469_; lean_object* v___x_470_; lean_object* v_env_471_; uint8_t v___x_472_; 
v___x_467_ = lean_st_ref_get(v___y_445_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v_k_469_ = l_Lean_mkPrivateName(v_env_468_, v_k_443_);
lean_dec_ref(v_env_468_);
v___x_470_ = lean_st_ref_get(v___y_445_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref(v_env_471_);
lean_dec(v___x_470_);
lean_inc(v_k_469_);
v___x_472_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_471_, v_k_469_);
if (v___x_472_ == 0)
{
lean_dec(v_k_469_);
v___y_448_ = v___y_444_;
v___y_449_ = v___y_445_;
goto v___jp_447_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_k_469_);
return v___x_473_;
}
}
else
{
v___y_457_ = v___x_454_;
goto v___jp_456_;
}
}
}
else
{
lean_object* v___x_476_; 
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_k_443_);
return v___x_476_;
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
lean_dec_ref_known(v___x_489_, 1);
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
lean_object* v_toCold_509_; lean_object* v_currNamespace_510_; lean_object* v___x_511_; 
v_toCold_509_ = lean_ctor_get(v_a_506_, 0);
v_currNamespace_510_ = lean_ctor_get(v_toCold_509_, 4);
lean_inc(v_currNamespace_510_);
v___x_511_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_505_, v_currNamespace_510_, v_a_506_, v_a_507_);
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
lean_dec_ref_known(v___x_540_, 1);
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
lean_dec_ref_known(v___x_551_, 1);
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
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Lean_PersistentArray_push___redArg(v_trees_697_, v_t_673_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_assignment_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_lazyAssignment_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v___x_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*3, v_enabled_694_);
v___x_704_ = v_reuseFailAlloc_710_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 7, v___x_704_);
v___x_706_ = v___x_692_;
goto v_reusejp_705_;
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
lean_ctor_set(v_reuseFailAlloc_709_, 7, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_709_, 8, v_snapshotTasks_690_);
v___x_706_ = v_reuseFailAlloc_709_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_st_ref_put(v___y_674_, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_701_);
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
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_env_770_; uint8_t v___x_771_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_st_ref_get(v___y_766_);
v_env_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_env_770_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Name_isAnonymous(v_declHint_765_);
if (v___x_771_ == 0)
{
uint8_t v_isExporting_772_; 
v_isExporting_772_ = lean_ctor_get_uint8(v_env_770_, sizeof(void*)*8);
if (v_isExporting_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v_env_770_);
lean_dec(v_declHint_765_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_msg_764_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
lean_inc_ref(v_env_770_);
v___x_774_ = l_Lean_Environment_setExporting(v_env_770_, v___x_771_);
lean_inc(v_declHint_765_);
lean_inc_ref(v___x_774_);
v___x_775_ = l_Lean_Environment_contains(v___x_774_, v_declHint_765_, v_isExporting_772_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v___x_774_);
lean_dec_ref(v_env_770_);
lean_dec(v_declHint_765_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_msg_764_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_c_782_; lean_object* v___x_783_; 
v___x_777_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
v___x_778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
v___x_779_ = l_Lean_Options_empty;
v___x_780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_780_, 0, v___x_774_);
lean_ctor_set(v___x_780_, 1, v___x_777_);
lean_ctor_set(v___x_780_, 2, v___x_778_);
lean_ctor_set(v___x_780_, 3, v___x_779_);
lean_inc(v_declHint_765_);
v___x_781_ = l_Lean_MessageData_ofConstName(v_declHint_765_, v___x_771_);
v_c_782_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_782_, 0, v___x_780_);
lean_ctor_set(v_c_782_, 1, v___x_781_);
v___x_783_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_770_, v_declHint_765_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_env_770_);
lean_dec(v_declHint_765_);
v___x_784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_c_782_);
v___x_786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_MessageData_note(v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v_msg_764_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_825_; 
v_val_791_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_825_ == 0)
{
v___x_793_ = v___x_783_;
v_isShared_794_ = v_isSharedCheck_825_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v___x_783_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_825_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_mod_797_; uint8_t v___x_798_; 
v___x_795_ = l_Lean_Environment_header(v_env_770_);
lean_dec_ref(v_env_770_);
v___x_796_ = l_Lean_EnvironmentHeader_moduleNames(v___x_795_);
v_mod_797_ = lean_array_get(v___x_768_, v___x_796_, v_val_791_);
lean_dec(v_val_791_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_isPrivateName(v_declHint_765_);
lean_dec(v_declHint_765_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_c_782_);
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
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
lean_ctor_set(v___x_793_, 0, v___x_808_);
v___x_810_ = v___x_793_;
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
lean_ctor_set(v___x_813_, 1, v_c_782_);
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
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
lean_ctor_set(v___x_793_, 0, v___x_821_);
v___x_823_ = v___x_793_;
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
lean_dec_ref(v_env_770_);
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
lean_object* v_toCold_859_; lean_object* v_currRecDepth_860_; lean_object* v_ref_861_; uint8_t v_diag_862_; uint8_t v_suppressElabErrors_863_; lean_object* v_ref_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_toCold_859_ = lean_ctor_get(v___y_856_, 0);
v_currRecDepth_860_ = lean_ctor_get(v___y_856_, 1);
v_ref_861_ = lean_ctor_get(v___y_856_, 2);
v_diag_862_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*3);
v_suppressElabErrors_863_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*3 + 1);
v_ref_864_ = l_Lean_replaceRef(v_ref_854_, v_ref_861_);
lean_inc(v_currRecDepth_860_);
lean_inc_ref(v_toCold_859_);
v___x_865_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_865_, 0, v_toCold_859_);
lean_ctor_set(v___x_865_, 1, v_currRecDepth_860_);
lean_ctor_set(v___x_865_, 2, v_ref_864_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*3, v_diag_862_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*3 + 1, v_suppressElabErrors_863_);
v___x_866_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_855_, v___x_865_, v___y_857_);
lean_dec_ref_known(v___x_865_, 3);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_867_, lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_867_, v_msg_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v_ref_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(lean_object* v_ref_873_, lean_object* v_msg_874_, lean_object* v_declHint_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_881_; 
v___x_879_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_874_, v_declHint_875_, v___y_876_, v___y_877_);
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_873_, v_a_880_, v___y_876_, v___y_877_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_ref_882_, lean_object* v_msg_883_, lean_object* v_declHint_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_882_, v_msg_883_, v_declHint_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_ref_882_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(lean_object* v_ref_892_, lean_object* v_constName_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_897_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
v___x_898_ = 0;
lean_inc(v_constName_893_);
v___x_899_ = l_Lean_MessageData_ofConstName(v_constName_893_, v___x_898_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_obj_once(&l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3, &l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once, _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_892_, v___x_902_, v_constName_893_, v___y_894_, v___y_895_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(lean_object* v_ref_904_, lean_object* v_constName_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_904_, v_constName_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v_ref_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* v_constName_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_ref_914_; lean_object* v___x_915_; 
v_ref_914_ = lean_ctor_get(v___y_911_, 2);
v___x_915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_914_, v_constName_910_, v___y_911_, v___y_912_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_constName_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(lean_object* v_constName_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v_env_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_st_ref_get(v___y_923_);
v_env_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc_ref(v_env_926_);
lean_dec(v___x_925_);
v___x_927_ = 0;
lean_inc(v_constName_921_);
v___x_928_ = l_Lean_Environment_findConstVal_x3f(v_env_926_, v_constName_921_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_921_, v___y_922_, v___y_923_);
return v___x_929_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_constName_921_);
v_val_930_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_928_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v___x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
if (lean_obj_tag(v_a_943_) == 0)
{
lean_object* v___x_945_; 
v___x_945_ = l_List_reverse___redArg(v_a_944_);
return v___x_945_;
}
else
{
lean_object* v_head_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_956_; 
v_head_946_ = lean_ctor_get(v_a_943_, 0);
v_tail_947_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_956_ == 0)
{
v___x_949_ = v_a_943_;
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_head_946_);
lean_dec(v_a_943_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Lean_mkLevelParam(v_head_946_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_944_);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_944_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_943_ = v_tail_947_;
v_a_944_ = v___x_953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(lean_object* v_constName_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
lean_inc(v_constName_957_);
v___x_961_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_levelParams_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v_levelParams_966_ = lean_ctor_get(v_a_962_, 1);
lean_inc(v_levelParams_966_);
lean_dec(v_a_962_);
v___x_967_ = lean_box(0);
v___x_968_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_966_, v___x_967_);
v___x_969_ = l_Lean_mkConst(v_constName_957_, v___x_968_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_969_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_constName_957_);
v_a_974_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_961_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_961_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(lean_object* v_constName_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(lean_object* v_stx_987_, lean_object* v_n_988_, lean_object* v_expectedType_x3f_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_988_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_stx_987_);
v___x_997_ = l_Lean_LocalContext_empty;
v___x_998_ = 0;
v___x_999_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v_expectedType_x3f_989_);
lean_ctor_set(v___x_999_, 3, v_a_994_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*4, v___x_998_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*4 + 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
v___x_1001_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_1000_, v___y_990_, v___y_991_);
return v___x_1001_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_expectedType_x3f_989_);
lean_dec(v_stx_987_);
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(lean_object* v_stx_1010_, lean_object* v_n_1011_, lean_object* v_expectedType_x3f_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v_stx_1010_, v_n_1011_, v_expectedType_x3f_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(lean_object* v_keys_1017_, lean_object* v_i_1018_, lean_object* v_k_1019_){
_start:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_array_get_size(v_keys_1017_);
v___x_1021_ = lean_nat_dec_lt(v_i_1018_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_dec(v_i_1018_);
return v___x_1021_;
}
else
{
lean_object* v_k_x27_1022_; uint8_t v___x_1023_; 
v_k_x27_1022_ = lean_array_fget_borrowed(v_keys_1017_, v_i_1018_);
v___x_1023_ = l_Lean_instBEqExtraModUse_beq(v_k_1019_, v_k_x27_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_add(v_i_1018_, v___x_1024_);
lean_dec(v_i_1018_);
v_i_1018_ = v___x_1025_;
goto _start;
}
else
{
lean_dec(v_i_1018_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_keys_1027_, lean_object* v_i_1028_, lean_object* v_k_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1027_, v_i_1028_, v_k_1029_);
lean_dec_ref(v_k_1029_);
lean_dec_ref(v_keys_1027_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1032_, size_t v_x_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 0)
{
lean_object* v_es_1035_; lean_object* v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v_j_1039_; lean_object* v___x_1040_; 
v_es_1035_ = lean_ctor_get(v_x_1032_, 0);
v___x_1036_ = lean_box(2);
v___x_1037_ = ((size_t)31ULL);
v___x_1038_ = lean_usize_land(v_x_1033_, v___x_1037_);
v_j_1039_ = lean_usize_to_nat(v___x_1038_);
v___x_1040_ = lean_array_get_borrowed(v___x_1036_, v_es_1035_, v_j_1039_);
lean_dec(v_j_1039_);
switch(lean_obj_tag(v___x_1040_))
{
case 0:
{
lean_object* v_key_1041_; uint8_t v___x_1042_; 
v_key_1041_ = lean_ctor_get(v___x_1040_, 0);
v___x_1042_ = l_Lean_instBEqExtraModUse_beq(v_x_1034_, v_key_1041_);
return v___x_1042_;
}
case 1:
{
lean_object* v_node_1043_; size_t v___x_1044_; size_t v___x_1045_; 
v_node_1043_ = lean_ctor_get(v___x_1040_, 0);
v___x_1044_ = ((size_t)5ULL);
v___x_1045_ = lean_usize_shift_right(v_x_1033_, v___x_1044_);
v_x_1032_ = v_node_1043_;
v_x_1033_ = v___x_1045_;
goto _start;
}
default: 
{
uint8_t v___x_1047_; 
v___x_1047_ = 0;
return v___x_1047_;
}
}
}
else
{
lean_object* v_ks_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_ks_1048_ = lean_ctor_get(v_x_1032_, 0);
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_1048_, v___x_1049_, v_x_1034_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
size_t v_x_6432__boxed_1054_; uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_x_6432__boxed_1054_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1055_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1051_, v_x_6432__boxed_1054_, v_x_1053_);
lean_dec_ref(v_x_1053_);
lean_dec_ref(v_x_1051_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
uint64_t v___x_1059_; size_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = l_Lean_instHashableExtraModUse_hash(v_x_1058_);
v___x_1060_ = lean_uint64_to_usize(v___x_1059_);
v___x_1061_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1057_, v___x_1060_, v_x_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1062_, v_x_1063_);
lean_dec_ref(v_x_1063_);
lean_dec_ref(v_x_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1066_; double v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_float_of_nat(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(lean_object* v_cls_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_ref_1076_; lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1122_; 
v_ref_1076_ = lean_ctor_get(v___y_1073_, 2);
v___x_1077_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_1072_, v___y_1073_, v___y_1074_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1122_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1122_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_traceState_1083_; lean_object* v_env_1084_; lean_object* v_nextMacroScope_1085_; lean_object* v_ngen_1086_; lean_object* v_auxDeclNGen_1087_; lean_object* v_cache_1088_; lean_object* v_messages_1089_; lean_object* v_infoState_1090_; lean_object* v_snapshotTasks_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1121_; 
v___x_1082_ = lean_st_ref_take(v___y_1074_);
v_traceState_1083_ = lean_ctor_get(v___x_1082_, 4);
v_env_1084_ = lean_ctor_get(v___x_1082_, 0);
v_nextMacroScope_1085_ = lean_ctor_get(v___x_1082_, 1);
v_ngen_1086_ = lean_ctor_get(v___x_1082_, 2);
v_auxDeclNGen_1087_ = lean_ctor_get(v___x_1082_, 3);
v_cache_1088_ = lean_ctor_get(v___x_1082_, 5);
v_messages_1089_ = lean_ctor_get(v___x_1082_, 6);
v_infoState_1090_ = lean_ctor_get(v___x_1082_, 7);
v_snapshotTasks_1091_ = lean_ctor_get(v___x_1082_, 8);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1093_ = v___x_1082_;
v_isShared_1094_ = v_isSharedCheck_1121_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snapshotTasks_1091_);
lean_inc(v_infoState_1090_);
lean_inc(v_messages_1089_);
lean_inc(v_cache_1088_);
lean_inc(v_traceState_1083_);
lean_inc(v_auxDeclNGen_1087_);
lean_inc(v_ngen_1086_);
lean_inc(v_nextMacroScope_1085_);
lean_inc(v_env_1084_);
lean_dec(v___x_1082_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1121_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint64_t v_tid_1095_; lean_object* v_traces_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1120_; 
v_tid_1095_ = lean_ctor_get_uint64(v_traceState_1083_, sizeof(void*)*1);
v_traces_1096_ = lean_ctor_get(v_traceState_1083_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_traceState_1083_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1098_ = v_traceState_1083_;
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_traces_1096_);
lean_dec(v_traceState_1083_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1120_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; double v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
v___x_1103_ = 0;
v___x_1104_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1105_, 0, v_cls_1071_);
lean_ctor_set(v___x_1105_, 1, v___x_1101_);
lean_ctor_set(v___x_1105_, 2, v___x_1104_);
lean_ctor_set_float(v___x_1105_, sizeof(void*)*3, v___x_1102_);
lean_ctor_set_float(v___x_1105_, sizeof(void*)*3 + 8, v___x_1102_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3 + 16, v___x_1103_);
v___x_1106_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2));
v___x_1107_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v_a_1078_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
lean_inc(v_ref_1076_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_ref_1076_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_PersistentArray_push___redArg(v_traces_1096_, v___x_1108_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1109_);
v___x_1111_ = v___x_1098_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1109_);
lean_ctor_set_uint64(v_reuseFailAlloc_1119_, sizeof(void*)*1, v_tid_1095_);
v___x_1111_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 4, v___x_1111_);
v___x_1113_ = v___x_1093_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_env_1084_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_nextMacroScope_1085_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_ngen_1086_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_auxDeclNGen_1087_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1118_, 5, v_cache_1088_);
lean_ctor_set(v_reuseFailAlloc_1118_, 6, v_messages_1089_);
lean_ctor_set(v_reuseFailAlloc_1118_, 7, v_infoState_1090_);
lean_ctor_set(v_reuseFailAlloc_1118_, 8, v_snapshotTasks_1091_);
v___x_1113_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_st_ref_put(v___y_1074_, v___x_1113_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1100_);
v___x_1116_ = v___x_1080_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1100_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1123_, lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1123_, v_msg_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1128_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v_cls_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_cls_1148_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1149_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1150_ = l_Lean_Name_append(v___x_1149_, v_cls_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(lean_object* v_mod_1161_, uint8_t v_isMeta_1162_, lean_object* v_hint_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_env_1169_; uint8_t v_isExporting_1170_; lean_object* v_entry_1171_; lean_object* v___x_1172_; lean_object* v_env_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___y_1178_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1167_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0);
v___x_1168_ = lean_st_ref_get(v___y_1165_);
v_env_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_env_1169_);
lean_dec(v___x_1168_);
v_isExporting_1170_ = lean_ctor_get_uint8(v_env_1169_, sizeof(void*)*8);
lean_dec_ref(v_env_1169_);
lean_inc(v_mod_1161_);
v_entry_1171_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1171_, 0, v_mod_1161_);
lean_ctor_set_uint8(v_entry_1171_, sizeof(void*)*1, v_isExporting_1170_);
lean_ctor_set_uint8(v_entry_1171_, sizeof(void*)*1 + 1, v_isMeta_1162_);
v___x_1172_ = lean_st_ref_get(v___y_1165_);
v_env_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_ref(v_env_1173_);
lean_dec(v___x_1172_);
v___x_1174_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1175_ = lean_box(1);
v___x_1176_ = lean_box(0);
v___x_1203_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1167_, v___x_1174_, v_env_1173_, v___x_1175_, v___x_1176_);
v___x_1204_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_1203_, v_entry_1171_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v_toCold_1205_; lean_object* v_options_1206_; uint8_t v_hasTrace_1207_; 
v_toCold_1205_ = lean_ctor_get(v___y_1164_, 0);
v_options_1206_ = lean_ctor_get(v_toCold_1205_, 2);
v_hasTrace_1207_ = lean_ctor_get_uint8(v_options_1206_, sizeof(void*)*1);
if (v_hasTrace_1207_ == 0)
{
lean_dec(v_hint_1163_);
lean_dec(v_mod_1161_);
v___y_1178_ = v___y_1165_;
goto v___jp_1177_;
}
else
{
lean_object* v_inheritedTraceOptions_1208_; lean_object* v_cls_1209_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_inheritedTraceOptions_1208_ = lean_ctor_get(v_toCold_1205_, 11);
v_cls_1209_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4));
v___x_1229_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
v___x_1230_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1208_, v_options_1206_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_hint_1163_);
lean_dec(v_mod_1161_);
v___y_1178_ = v___y_1165_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1231_; lean_object* v___y_1233_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14);
if (v_isExporting_1170_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19));
v___y_1233_ = v___x_1240_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20));
v___y_1233_ = v___x_1241_;
goto v___jp_1232_;
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_inc_ref(v___y_1233_);
v___x_1234_ = l_Lean_stringToMessageData(v___y_1233_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1231_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
if (v_isMeta_1162_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17));
v___y_1216_ = v___x_1237_;
v___y_1217_ = v___x_1238_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18));
v___y_1216_ = v___x_1237_;
v___y_1217_ = v___x_1239_;
goto v___jp_1215_;
}
}
}
v___jp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1211_);
lean_ctor_set(v___x_1213_, 1, v___y_1212_);
v___x_1214_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_1209_, v___x_1213_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref_known(v___x_1214_, 1);
v___y_1178_ = v___y_1165_;
goto v___jp_1177_;
}
else
{
lean_dec_ref_known(v_entry_1171_, 1);
return v___x_1214_;
}
}
v___jp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
lean_inc_ref(v___y_1217_);
v___x_1218_ = l_Lean_stringToMessageData(v___y_1217_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1216_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_MessageData_ofName(v_mod_1161_);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_Name_isAnonymous(v_hint_1163_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8);
v___x_1226_ = l_Lean_MessageData_ofName(v_hint_1163_);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___y_1211_ = v___x_1223_;
v___y_1212_ = v___x_1227_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_hint_1163_);
v___x_1228_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
v___y_1211_ = v___x_1223_;
v___y_1212_ = v___x_1228_;
goto v___jp_1210_;
}
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref_known(v_entry_1171_, 1);
lean_dec(v_hint_1163_);
lean_dec(v_mod_1161_);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
v___jp_1177_:
{
lean_object* v___x_1179_; lean_object* v_toEnvExtension_1180_; lean_object* v_env_1181_; lean_object* v_nextMacroScope_1182_; lean_object* v_ngen_1183_; lean_object* v_auxDeclNGen_1184_; lean_object* v_traceState_1185_; lean_object* v_messages_1186_; lean_object* v_infoState_1187_; lean_object* v_snapshotTasks_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1201_; 
v___x_1179_ = lean_st_ref_take(v___y_1178_);
v_toEnvExtension_1180_ = lean_ctor_get(v___x_1174_, 0);
v_env_1181_ = lean_ctor_get(v___x_1179_, 0);
v_nextMacroScope_1182_ = lean_ctor_get(v___x_1179_, 1);
v_ngen_1183_ = lean_ctor_get(v___x_1179_, 2);
v_auxDeclNGen_1184_ = lean_ctor_get(v___x_1179_, 3);
v_traceState_1185_ = lean_ctor_get(v___x_1179_, 4);
v_messages_1186_ = lean_ctor_get(v___x_1179_, 6);
v_infoState_1187_ = lean_ctor_get(v___x_1179_, 7);
v_snapshotTasks_1188_ = lean_ctor_get(v___x_1179_, 8);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1179_, 5);
lean_dec(v_unused_1202_);
v___x_1190_ = v___x_1179_;
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snapshotTasks_1188_);
lean_inc(v_infoState_1187_);
lean_inc(v_messages_1186_);
lean_inc(v_traceState_1185_);
lean_inc(v_auxDeclNGen_1184_);
lean_inc(v_ngen_1183_);
lean_inc(v_nextMacroScope_1182_);
lean_inc(v_env_1181_);
lean_dec(v___x_1179_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_asyncMode_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v_asyncMode_1192_ = lean_ctor_get(v_toEnvExtension_1180_, 2);
v___x_1193_ = lean_box(0);
v___x_1194_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1174_, v_env_1181_, v_entry_1171_, v_asyncMode_1192_, v___x_1176_);
v___x_1195_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 5, v___x_1195_);
lean_ctor_set(v___x_1190_, 0, v___x_1194_);
v___x_1197_ = v___x_1190_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_nextMacroScope_1182_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_ngen_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_auxDeclNGen_1184_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_traceState_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_messages_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_infoState_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_snapshotTasks_1188_);
v___x_1197_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_st_ref_put(v___y_1178_, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1193_);
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(lean_object* v_mod_1244_, lean_object* v_isMeta_1245_, lean_object* v_hint_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_isMeta_boxed_1250_; lean_object* v_res_1251_; 
v_isMeta_boxed_1250_ = lean_unbox(v_isMeta_1245_);
v_res_1251_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_1244_, v_isMeta_boxed_1250_, v_hint_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(lean_object* v___x_1252_, lean_object* v_declName_1253_, lean_object* v_as_1254_, size_t v_sz_1255_, size_t v_i_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_lt(v_i_1256_, v_sz_1255_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec(v_declName_1253_);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_b_1257_);
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; lean_object* v_modules_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1267_; lean_object* v_toImport_1268_; lean_object* v_module_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1263_ = l_Lean_Environment_header(v___x_1252_);
v_modules_1264_ = lean_ctor_get(v___x_1263_, 3);
lean_inc_ref(v_modules_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1266_ = lean_array_uget_borrowed(v_as_1254_, v_i_1256_);
v___x_1267_ = lean_array_get(v___x_1265_, v_modules_1264_, v_a_1266_);
lean_dec_ref(v_modules_1264_);
v_toImport_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc_ref(v_toImport_1268_);
lean_dec(v___x_1267_);
v_module_1269_ = lean_ctor_get(v_toImport_1268_, 0);
lean_inc(v_module_1269_);
lean_dec_ref(v_toImport_1268_);
v___x_1270_ = lean_box(0);
v___x_1271_ = 0;
lean_inc(v_declName_1253_);
v___x_1272_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1269_, v___x_1271_, v_declName_1253_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1272_) == 0)
{
size_t v___x_1273_; size_t v___x_1274_; 
lean_dec_ref_known(v___x_1272_, 1);
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1256_, v___x_1273_);
v_i_1256_ = v___x_1274_;
v_b_1257_ = v___x_1270_;
goto _start;
}
else
{
lean_dec(v_declName_1253_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(lean_object* v___x_1276_, lean_object* v_declName_1277_, lean_object* v_as_1278_, lean_object* v_sz_1279_, lean_object* v_i_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
size_t v_sz_boxed_1285_; size_t v_i_boxed_1286_; lean_object* v_res_1287_; 
v_sz_boxed_1285_ = lean_unbox_usize(v_sz_1279_);
lean_dec(v_sz_1279_);
v_i_boxed_1286_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_1276_, v_declName_1277_, v_as_1278_, v_sz_boxed_1285_, v_i_boxed_1286_, v_b_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_as_1278_);
lean_dec_ref(v___x_1276_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
else
{
lean_object* v_key_1291_; lean_object* v_value_1292_; lean_object* v_tail_1293_; uint8_t v___x_1294_; 
v_key_1291_ = lean_ctor_get(v_x_1289_, 0);
v_value_1292_ = lean_ctor_get(v_x_1289_, 1);
v_tail_1293_ = lean_ctor_get(v_x_1289_, 2);
v___x_1294_ = lean_name_eq(v_key_1291_, v_a_1288_);
if (v___x_1294_ == 0)
{
v_x_1289_ = v_tail_1293_;
goto _start;
}
else
{
lean_object* v___x_1296_; 
lean_inc(v_value_1292_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_value_1292_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec(v_a_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_buckets_1302_; lean_object* v___x_1303_; uint64_t v___y_1305_; 
v_buckets_1302_ = lean_ctor_get(v_m_1300_, 1);
v___x_1303_ = lean_array_get_size(v_buckets_1302_);
if (lean_obj_tag(v_a_1301_) == 0)
{
uint64_t v___x_1319_; 
v___x_1319_ = 1723ULL;
v___y_1305_ = v___x_1319_;
goto v___jp_1304_;
}
else
{
uint64_t v_hash_1320_; 
v_hash_1320_ = lean_ctor_get_uint64(v_a_1301_, sizeof(void*)*2);
v___y_1305_ = v_hash_1320_;
goto v___jp_1304_;
}
v___jp_1304_:
{
uint64_t v___x_1306_; uint64_t v___x_1307_; uint64_t v_fold_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1306_ = 32ULL;
v___x_1307_ = lean_uint64_shift_right(v___y_1305_, v___x_1306_);
v_fold_1308_ = lean_uint64_xor(v___y_1305_, v___x_1307_);
v___x_1309_ = 16ULL;
v___x_1310_ = lean_uint64_shift_right(v_fold_1308_, v___x_1309_);
v___x_1311_ = lean_uint64_xor(v_fold_1308_, v___x_1310_);
v___x_1312_ = lean_uint64_to_usize(v___x_1311_);
v___x_1313_ = lean_usize_of_nat(v___x_1303_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_sub(v___x_1313_, v___x_1314_);
v___x_1316_ = lean_usize_land(v___x_1312_, v___x_1315_);
v___x_1317_ = lean_array_uget_borrowed(v_buckets_1302_, v___x_1316_);
v___x_1318_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1301_, v___x_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(lean_object* v_m_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_m_1321_);
return v_res_1323_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(lean_object* v_declName_1327_, uint8_t v_isMeta_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_env_1337_; lean_object* v___y_1339_; lean_object* v___x_1352_; 
v___x_1332_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0);
v___x_1333_ = lean_st_ref_get(v___y_1330_);
v_env_1337_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_ref(v_env_1337_);
lean_dec(v___x_1333_);
v___x_1352_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1337_, v_declName_1327_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_dec_ref(v_env_1337_);
lean_dec(v_declName_1327_);
goto v___jp_1334_;
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1354_; lean_object* v_modules_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_Environment_header(v_env_1337_);
v_modules_1355_ = lean_ctor_get(v___x_1354_, 3);
lean_inc_ref(v_modules_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = lean_array_get_size(v_modules_1355_);
v___x_1357_ = lean_nat_dec_lt(v_val_1353_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec_ref(v_modules_1355_);
lean_dec(v_val_1353_);
lean_dec_ref(v_env_1337_);
lean_dec(v_declName_1327_);
goto v___jp_1334_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___y_1361_; 
v___x_1358_ = lean_array_fget(v_modules_1355_, v_val_1353_);
lean_dec(v_val_1353_);
lean_dec_ref(v_modules_1355_);
v___x_1359_ = lean_st_ref_get(v___y_1330_);
if (v_isMeta_1328_ == 0)
{
lean_dec(v___x_1359_);
v___y_1361_ = v_isMeta_1328_;
goto v___jp_1360_;
}
else
{
lean_object* v_env_1372_; uint8_t v___x_1373_; 
v_env_1372_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_ref(v_env_1372_);
lean_dec(v___x_1359_);
lean_inc(v_declName_1327_);
v___x_1373_ = l_Lean_isMarkedMeta(v_env_1372_, v_declName_1327_);
if (v___x_1373_ == 0)
{
v___y_1361_ = v_isMeta_1328_;
goto v___jp_1360_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = 0;
v___y_1361_ = v___x_1374_;
goto v___jp_1360_;
}
}
v___jp_1360_:
{
lean_object* v_toImport_1362_; lean_object* v_module_1363_; lean_object* v___x_1364_; 
v_toImport_1362_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_ref(v_toImport_1362_);
lean_dec(v___x_1358_);
v_module_1363_ = lean_ctor_get(v_toImport_1362_, 0);
lean_inc(v_module_1363_);
lean_dec_ref(v_toImport_1362_);
lean_inc(v_declName_1327_);
v___x_1364_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_1363_, v___y_1361_, v_declName_1327_, v___y_1329_, v___y_1330_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = l_Lean_indirectModUseExt;
v___x_1366_ = lean_box(1);
v___x_1367_ = lean_box(0);
lean_inc_ref(v_env_1337_);
v___x_1368_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1332_, v___x_1365_, v_env_1337_, v___x_1366_, v___x_1367_);
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_1368_, v_declName_1327_);
lean_dec(v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1));
v___y_1339_ = v___x_1370_;
goto v___jp_1338_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v___x_1369_, 1);
v___y_1339_ = v_val_1371_;
goto v___jp_1338_;
}
}
else
{
lean_dec_ref(v_env_1337_);
lean_dec(v_declName_1327_);
return v___x_1364_;
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
v___jp_1338_:
{
lean_object* v___x_1340_; size_t v_sz_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_box(0);
v_sz_1341_ = lean_array_size(v___y_1339_);
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_1337_, v_declName_1327_, v___y_1339_, v_sz_1341_, v___x_1342_, v___x_1340_, v___y_1329_, v___y_1330_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v_env_1337_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v___x_1343_, 0);
lean_dec(v_unused_1351_);
v___x_1345_ = v___x_1343_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v___x_1343_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1340_);
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1340_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(lean_object* v_declName_1375_, lean_object* v_isMeta_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
uint8_t v_isMeta_boxed_1380_; lean_object* v_res_1381_; 
v_isMeta_boxed_1380_ = lean_unbox(v_isMeta_1376_);
v_res_1381_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_declName_1375_, v_isMeta_boxed_1380_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1(lean_object* v_parserNamespace_1382_, uint8_t v_x_1383_, lean_object* v_stx_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
lean_inc(v_stx_1384_);
v___x_1388_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(v_parserNamespace_1382_, v_stx_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1441_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1441_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1441_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v_env_1394_; uint8_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1393_ = lean_st_ref_get(v___y_1386_);
v_env_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_ref(v_env_1394_);
lean_dec(v___x_1393_);
v___x_1395_ = 1;
lean_inc(v_a_1389_);
v___x_1396_ = l_Lean_Environment_contains(v_env_1394_, v_a_1389_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1398_; 
lean_dec(v_stx_1384_);
if (v_isShared_1392_ == 0)
{
v___x_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1389_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
uint8_t v___x_1400_; lean_object* v___x_1401_; 
lean_del_object(v___x_1391_);
v___x_1400_ = 0;
lean_inc(v_a_1389_);
v___x_1401_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(v_a_1389_, v___x_1400_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1432_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1431_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1431_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v_infoState_1406_; uint8_t v_enabled_1407_; 
v___x_1405_ = lean_st_ref_get(v___y_1386_);
v_infoState_1406_ = lean_ctor_get(v___x_1405_, 7);
lean_inc_ref(v_infoState_1406_);
lean_dec(v___x_1405_);
v_enabled_1407_ = lean_ctor_get_uint8(v_infoState_1406_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1406_);
if (v_enabled_1407_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_stx_1384_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_a_1389_);
v___x_1409_ = v___x_1403_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1389_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_del_object(v___x_1403_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = l_Lean_Syntax_getArg(v_stx_1384_, v___x_1411_);
lean_dec(v_stx_1384_);
v___x_1413_ = lean_box(0);
lean_inc(v_a_1389_);
v___x_1414_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(v___x_1412_, v_a_1389_, v___x_1413_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1422_);
v___x_1416_ = v___x_1414_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v___x_1414_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_a_1389_);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1389_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_a_1389_);
v_a_1423_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1414_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1414_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_a_1389_);
lean_dec(v_stx_1384_);
v_a_1433_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1401_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1401_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_1384_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(lean_object* v_parserNamespace_1442_, lean_object* v_x_1443_, lean_object* v_stx_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_x_6992__boxed_1448_; lean_object* v_res_1449_; 
v_x_6992__boxed_1448_ = lean_unbox(v_x_1443_);
v_res_1449_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(v_parserNamespace_1442_, v_x_6992__boxed_1448_, v_stx_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object* v_attrBuiltinName_1452_, lean_object* v_attrName_1453_, lean_object* v_parserNamespace_1454_, lean_object* v_typeName_1455_, lean_object* v_kind_1456_, lean_object* v_attrDeclName_1457_){
_start:
{
lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___f_1459_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__0));
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_1460_, 0, v_parserNamespace_1454_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_mkElabAttribute___redArg___closed__1));
v___x_1462_ = lean_string_append(v_kind_1456_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1463_, 0, v_attrBuiltinName_1452_);
lean_ctor_set(v___x_1463_, 1, v_attrName_1453_);
lean_ctor_set(v___x_1463_, 2, v___x_1462_);
lean_ctor_set(v___x_1463_, 3, v_typeName_1455_);
lean_ctor_set(v___x_1463_, 4, v___f_1460_);
lean_ctor_set(v___x_1463_, 5, v___f_1459_);
v___x_1464_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1463_, v_attrDeclName_1457_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___redArg___boxed(lean_object* v_attrBuiltinName_1465_, lean_object* v_attrName_1466_, lean_object* v_parserNamespace_1467_, lean_object* v_typeName_1468_, lean_object* v_kind_1469_, lean_object* v_attrDeclName_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1465_, v_attrName_1466_, v_parserNamespace_1467_, v_typeName_1468_, v_kind_1469_, v_attrDeclName_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute(lean_object* v_00_u03b3_1473_, lean_object* v_attrBuiltinName_1474_, lean_object* v_attrName_1475_, lean_object* v_parserNamespace_1476_, lean_object* v_typeName_1477_, lean_object* v_kind_1478_, lean_object* v_attrDeclName_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Elab_mkElabAttribute___redArg(v_attrBuiltinName_1474_, v_attrName_1475_, v_parserNamespace_1476_, v_typeName_1477_, v_kind_1478_, v_attrDeclName_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkElabAttribute___boxed(lean_object* v_00_u03b3_1482_, lean_object* v_attrBuiltinName_1483_, lean_object* v_attrName_1484_, lean_object* v_parserNamespace_1485_, lean_object* v_typeName_1486_, lean_object* v_kind_1487_, lean_object* v_attrDeclName_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Elab_mkElabAttribute(v_00_u03b3_1482_, v_attrBuiltinName_1483_, v_attrName_1484_, v_parserNamespace_1485_, v_typeName_1486_, v_kind_1487_, v_attrDeclName_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(lean_object* v_00_u03b2_1491_, lean_object* v_m_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_1492_, v_a_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1495_, lean_object* v_m_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_1495_, v_m_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_m_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(lean_object* v_t_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_1499_, v___y_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(lean_object* v_t_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_1510_, v_x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_1513_, v_x_1514_, v_x_1515_);
lean_dec_ref(v_x_1515_);
lean_dec_ref(v_x_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1518_, lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_1519_, v_x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_a_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_1522_, v_a_1523_, v_x_1524_);
lean_dec(v_x_1524_);
lean_dec(v_a_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1526_, lean_object* v_x_1527_, size_t v_x_1528_, lean_object* v_x_1529_){
_start:
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1527_, v_x_1528_, v_x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
size_t v_x_7162__boxed_1535_; uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_x_7162__boxed_1535_ = lean_unbox_usize(v_x_1533_);
lean_dec(v_x_1533_);
v_res_1536_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1531_, v_x_1532_, v_x_7162__boxed_1535_, v_x_1534_);
lean_dec_ref(v_x_1534_);
lean_dec_ref(v_x_1532_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(lean_object* v_00_u03b1_1538_, lean_object* v_constName_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_1539_, v___y_1540_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1544_, lean_object* v_constName_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_1544_, v_constName_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_heq_1553_, lean_object* v_i_1554_, lean_object* v_k_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_1551_, v_i_1554_, v_k_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_keys_1558_, lean_object* v_vals_1559_, lean_object* v_heq_1560_, lean_object* v_i_1561_, lean_object* v_k_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_1557_, v_keys_1558_, v_vals_1559_, v_heq_1560_, v_i_1561_, v_k_1562_);
lean_dec_ref(v_k_1562_);
lean_dec_ref(v_vals_1559_);
lean_dec_ref(v_keys_1558_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(lean_object* v_00_u03b1_1565_, lean_object* v_ref_1566_, lean_object* v_constName_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_1566_, v_constName_1567_, v___y_1568_, v___y_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1572_, lean_object* v_ref_1573_, lean_object* v_constName_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_1572_, v_ref_1573_, v_constName_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_ref_1573_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1579_, lean_object* v_ref_1580_, lean_object* v_msg_1581_, lean_object* v_declHint_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_1580_, v_msg_1581_, v_declHint_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1587_, lean_object* v_ref_1588_, lean_object* v_msg_1589_, lean_object* v_declHint_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_1587_, v_ref_1588_, v_msg_1589_, v_declHint_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v_ref_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(lean_object* v_msg_1595_, lean_object* v_declHint_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_1595_, v_declHint_1596_, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(lean_object* v_msg_1601_, lean_object* v_declHint_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_1601_, v_declHint_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1607_, lean_object* v_ref_1608_, lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_1608_, v_msg_1609_, v___y_1610_, v___y_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_ref_1615_, lean_object* v_msg_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_1614_, v_ref_1615_, v_msg_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v_ref_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe(lean_object* v_ref_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1));
v___x_1634_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2));
v___x_1635_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3));
v___x_1636_ = lean_box(0);
v___x_1637_ = ((lean_object*)(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5));
v___x_1638_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_1633_, v___x_1635_, v___x_1636_, v___x_1637_, v___x_1634_, v_ref_1631_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___boxed(lean_object* v_ref_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1649_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1(){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1655_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0));
v___x_1656_ = l_Lean_addBuiltinDocString(v___x_1654_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_));
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6));
v___x_1687_ = l_Lean_addBuiltinDeclarationRanges(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(lean_object* v_toOLeanEntry_1690_, lean_object* v_a_1691_, lean_object* v_____r_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_declName_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v_declName_1695_ = lean_ctor_get(v_toOLeanEntry_1690_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_toOLeanEntry_1690_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v_toOLeanEntry_1690_, 0);
lean_dec(v_unused_1707_);
v___x_1697_ = v_toOLeanEntry_1690_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_declName_1695_);
lean_dec(v_toOLeanEntry_1690_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_a_1691_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1699_);
lean_ctor_set(v___x_1697_, 0, v_declName_1695_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_declName_1695_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___y_1694_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_toOLeanEntry_1708_, lean_object* v_a_1709_, lean_object* v_____r_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1708_, v_a_1709_, v_____r_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(lean_object* v_stx_1717_, lean_object* v_as_x27_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
if (lean_obj_tag(v_as_x27_1718_) == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_stx_1717_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1719_);
lean_ctor_set(v___x_1722_, 1, v___y_1721_);
return v___x_1722_;
}
else
{
lean_object* v_head_1723_; lean_object* v_tail_1724_; lean_object* v_toOLeanEntry_1725_; uint8_t v_isBuiltin_1726_; lean_object* v_value_1727_; lean_object* v_macroScope_1728_; lean_object* v_traceMsgs_1729_; lean_object* v_expandedMacroDecls_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_b_1719_);
v_head_1723_ = lean_ctor_get(v_as_x27_1718_, 0);
v_tail_1724_ = lean_ctor_get(v_as_x27_1718_, 1);
v_toOLeanEntry_1725_ = lean_ctor_get(v_head_1723_, 0);
v_isBuiltin_1726_ = lean_ctor_get_uint8(v_head_1723_, sizeof(void*)*2);
v_value_1727_ = lean_ctor_get(v_head_1723_, 1);
v_macroScope_1728_ = lean_ctor_get(v___y_1721_, 0);
v_traceMsgs_1729_ = lean_ctor_get(v___y_1721_, 1);
v_expandedMacroDecls_1730_ = lean_ctor_get(v___y_1721_, 2);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___y_1721_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1732_ = v___y_1721_;
v_isShared_1733_ = v_isSharedCheck_1795_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_expandedMacroDecls_1730_);
lean_inc(v_traceMsgs_1729_);
lean_inc(v_macroScope_1728_);
lean_dec(v___y_1721_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1795_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_methods_1734_; lean_object* v_quotContext_1735_; lean_object* v_currRecDepth_1736_; lean_object* v_maxRecDepth_1737_; lean_object* v_ref_1738_; lean_object* v___x_1739_; lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v___x_1746_; lean_object* v_a_1748_; lean_object* v_a_1749_; lean_object* v___y_1756_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v_methods_1734_ = lean_ctor_get(v___y_1720_, 0);
v_quotContext_1735_ = lean_ctor_get(v___y_1720_, 1);
v_currRecDepth_1736_ = lean_ctor_get(v___y_1720_, 3);
v_maxRecDepth_1737_ = lean_ctor_get(v___y_1720_, 4);
v_ref_1738_ = lean_ctor_get(v___y_1720_, 5);
v___x_1739_ = lean_box(0);
v___x_1746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_macroScope_1728_, v___x_1762_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1763_);
v___x_1765_ = v___x_1732_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_traceMsgs_1729_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_expandedMacroDecls_1730_);
v___x_1765_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1764_;
}
v___jp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1741_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1739_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1742_);
return v___x_1745_;
}
v___jp_1747_:
{
if (lean_obj_tag(v_a_1748_) == 1)
{
v_as_x27_1718_ = v_tail_1724_;
v_b_1719_ = v___x_1746_;
v___y_1721_ = v_a_1749_;
goto _start;
}
else
{
lean_object* v_declName_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_stx_1717_);
v_declName_1751_ = lean_ctor_get(v_toOLeanEntry_1725_, 1);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1748_);
lean_inc(v_declName_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_declName_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v_a_1741_ = v___x_1754_;
v_a_1742_ = v_a_1749_;
goto v___jp_1740_;
}
}
v___jp_1755_:
{
lean_object* v_a_1757_; 
v_a_1757_ = lean_ctor_get(v___y_1756_, 0);
if (lean_obj_tag(v_a_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v_a_1759_; 
lean_inc_ref(v_a_1757_);
lean_dec(v_stx_1717_);
v_a_1758_ = lean_ctor_get(v___y_1756_, 1);
lean_inc(v_a_1758_);
lean_dec_ref(v___y_1756_);
v_a_1759_ = lean_ctor_get(v_a_1757_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v_a_1757_, 1);
v_a_1741_ = v_a_1759_;
v_a_1742_ = v_a_1758_;
goto v___jp_1740_;
}
else
{
lean_object* v_a_1760_; 
v_a_1760_ = lean_ctor_get(v___y_1756_, 1);
lean_inc(v_a_1760_);
lean_dec_ref(v___y_1756_);
v_as_x27_1718_ = v_tail_1724_;
v_b_1719_ = v___x_1746_;
v___y_1721_ = v_a_1760_;
goto _start;
}
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_inc(v_ref_1738_);
lean_inc(v_maxRecDepth_1737_);
lean_inc(v_currRecDepth_1736_);
lean_inc(v_quotContext_1735_);
lean_inc(v_methods_1734_);
v___x_1766_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1766_, 0, v_methods_1734_);
lean_ctor_set(v___x_1766_, 1, v_quotContext_1735_);
lean_ctor_set(v___x_1766_, 2, v_macroScope_1728_);
lean_ctor_set(v___x_1766_, 3, v_currRecDepth_1736_);
lean_ctor_set(v___x_1766_, 4, v_maxRecDepth_1737_);
lean_ctor_set(v___x_1766_, 5, v_ref_1738_);
lean_inc(v_value_1727_);
lean_inc(v_stx_1717_);
v___x_1767_ = lean_apply_3(v_value_1727_, v_stx_1717_, v___x_1766_, v___x_1765_);
if (lean_obj_tag(v___x_1767_) == 0)
{
if (v_isBuiltin_1726_ == 0)
{
lean_object* v_a_1768_; lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 1);
v_a_1769_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1768_);
lean_inc(v_a_1769_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_macroScope_1773_; lean_object* v_traceMsgs_1774_; lean_object* v_expandedMacroDecls_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1787_; 
v_macroScope_1773_ = lean_ctor_get(v_a_1768_, 0);
v_traceMsgs_1774_ = lean_ctor_get(v_a_1768_, 1);
v_expandedMacroDecls_1775_ = lean_ctor_get(v_a_1768_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_a_1768_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1777_ = v_a_1768_;
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_expandedMacroDecls_1775_);
lean_inc(v_traceMsgs_1774_);
lean_inc(v_macroScope_1773_);
lean_dec(v_a_1768_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_declName_1779_; lean_object* v___x_1781_; 
v_declName_1779_ = lean_ctor_get(v_toOLeanEntry_1725_, 1);
lean_inc(v_declName_1779_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 1);
lean_ctor_set(v___x_1771_, 1, v_expandedMacroDecls_1775_);
lean_ctor_set(v___x_1771_, 0, v_declName_1779_);
v___x_1781_ = v___x_1771_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_declName_1779_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_expandedMacroDecls_1775_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 2, v___x_1781_);
v___x_1783_ = v___x_1777_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_macroScope_1773_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_traceMsgs_1774_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; 
lean_inc_ref(v_toOLeanEntry_1725_);
v___x_1784_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1725_, v_a_1769_, v___x_1739_, v___y_1720_, v___x_1783_);
v___y_1756_ = v___x_1784_;
goto v___jp_1755_;
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1789_);
v_a_1790_ = lean_ctor_get(v___x_1767_, 1);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1767_, 2);
lean_inc_ref(v_toOLeanEntry_1725_);
v___x_1791_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_1725_, v_a_1789_, v___x_1739_, v___y_1720_, v_a_1790_);
v___y_1756_ = v___x_1791_;
goto v___jp_1755_;
}
}
else
{
lean_object* v_a_1792_; lean_object* v_a_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1792_);
v_a_1793_ = lean_ctor_get(v___x_1767_, 1);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1767_, 2);
v_a_1748_ = v_a_1792_;
v_a_1749_ = v_a_1793_;
goto v___jp_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(lean_object* v_stx_1796_, lean_object* v_as_x27_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1796_, v_as_x27_1797_, v_b_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v_as_x27_1797_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object* v_env_1802_, lean_object* v_stx_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v_a_1812_; lean_object* v_fst_1813_; 
v___x_1806_ = l_Lean_Elab_macroAttribute;
lean_inc(v_stx_1803_);
v___x_1807_ = l_Lean_Syntax_getKind(v_stx_1803_);
v___x_1808_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_1806_, v_env_1802_, v___x_1807_);
lean_dec(v___x_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0));
v___x_1811_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1803_, v___x_1808_, v___x_1810_, v_a_1804_, v_a_1805_);
lean_dec(v___x_1808_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
v_fst_1813_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_fst_1813_);
lean_dec(v_a_1812_);
if (lean_obj_tag(v_fst_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1811_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1822_);
v___x_1816_ = v___x_1811_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1811_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1809_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1831_; 
v_a_1823_ = lean_ctor_get(v___x_1811_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1832_);
v___x_1825_ = v___x_1811_;
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1811_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_val_1827_; lean_object* v___x_1829_; 
v_val_1827_ = lean_ctor_get(v_fst_1813_, 0);
lean_inc(v_val_1827_);
lean_dec_ref_known(v_fst_1813_, 1);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_val_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_val_1827_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_a_1823_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object* v_env_1833_, lean_object* v_stx_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1833_, v_stx_1834_, v_a_1835_, v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(lean_object* v_stx_1838_, lean_object* v_as_1839_, lean_object* v_as_x27_1840_, lean_object* v_b_1841_, lean_object* v_a_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(v_stx_1838_, v_as_x27_1840_, v_b_1841_, v___y_1843_, v___y_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(lean_object* v_stx_1846_, lean_object* v_as_1847_, lean_object* v_as_x27_1848_, lean_object* v_b_1849_, lean_object* v_a_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(v_stx_1846_, v_as_1847_, v_as_x27_1848_, v_b_1849_, v_a_1850_, v___y_1851_, v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v_as_x27_1848_);
lean_dec(v_as_1847_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(lean_object* v_setNextMacroScope_1854_, lean_object* v_inst_1855_, lean_object* v_s_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_apply_1(v_setNextMacroScope_1854_, v_s_1856_);
v___x_1858_ = lean_apply_2(v_inst_1855_, lean_box(0), v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_){
_start:
{
lean_object* v_getNextMacroScope_1862_; lean_object* v_setNextMacroScope_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
v_getNextMacroScope_1862_ = lean_ctor_get(v_inst_1861_, 1);
v_setNextMacroScope_1863_ = lean_ctor_get(v_inst_1861_, 2);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_inst_1861_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v_inst_1861_, 0);
lean_dec(v_unused_1873_);
v___x_1865_ = v_inst_1861_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_setNextMacroScope_1863_);
lean_inc(v_getNextMacroScope_1862_);
lean_dec(v_inst_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___f_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_inc(v_inst_1859_);
v___f_1867_ = lean_alloc_closure((void*)(l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1867_, 0, v_setNextMacroScope_1863_);
lean_closure_set(v___f_1867_, 1, v_inst_1859_);
v___x_1868_ = lean_apply_2(v_inst_1859_, lean_box(0), v_getNextMacroScope_1862_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 2, v___f_1867_);
lean_ctor_set(v___x_1865_, 1, v___x_1868_);
lean_ctor_set(v___x_1865_, 0, v_inst_1860_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_inst_1860_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v___f_1867_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(lean_object* v_m_1874_, lean_object* v_n_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0(lean_object* v_toPure_1891_, lean_object* v_fst_1892_, lean_object* v_____do__lift_1893_, lean_object* v_____do__lift_1894_){
_start:
{
uint8_t v_hasTrace_1895_; 
v_hasTrace_1895_ = lean_ctor_get_uint8(v_____do__lift_1894_, sizeof(void*)*1);
if (v_hasTrace_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_fst_1892_);
v___x_1896_ = lean_box(v_hasTrace_1895_);
v___x_1897_ = lean_apply_2(v_toPure_1891_, lean_box(0), v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1898_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11));
v___x_1899_ = l_Lean_Name_append(v___x_1898_, v_fst_1892_);
v___x_1900_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1893_, v_____do__lift_1894_, v___x_1899_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_box(v___x_1900_);
v___x_1902_ = lean_apply_2(v_toPure_1891_, lean_box(0), v___x_1901_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(lean_object* v_toPure_1903_, lean_object* v_fst_1904_, lean_object* v_____do__lift_1905_, lean_object* v_____do__lift_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Elab_liftMacroM___redArg___lam__0(v_toPure_1903_, v_fst_1904_, v_____do__lift_1905_, v_____do__lift_1906_);
lean_dec_ref(v_____do__lift_1906_);
lean_dec_ref(v_____do__lift_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__1(lean_object* v_toPure_1908_, lean_object* v_fst_1909_, lean_object* v_toBind_1910_, lean_object* v_inst_1911_, lean_object* v_____do__lift_1912_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; 
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1913_, 0, v_toPure_1908_);
lean_closure_set(v___f_1913_, 1, v_fst_1909_);
lean_closure_set(v___f_1913_, 2, v_____do__lift_1912_);
v___x_1914_ = lean_apply_4(v_toBind_1910_, lean_box(0), lean_box(0), v_inst_1911_, v___f_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2(lean_object* v_toPure_1915_, lean_object* v_snd_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_toMonadRef_1919_, lean_object* v_inst_1920_, lean_object* v_fst_1921_, uint8_t v_____do__lift_1922_){
_start:
{
if (v_____do__lift_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v_fst_1921_);
lean_dec(v_inst_1920_);
lean_dec_ref(v_toMonadRef_1919_);
lean_dec_ref(v_inst_1918_);
lean_dec_ref(v_inst_1917_);
lean_dec_ref(v_snd_1916_);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_apply_2(v_toPure_1915_, lean_box(0), v___x_1923_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_toPure_1915_);
v___x_1925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_snd_1916_);
v___x_1926_ = l_Lean_MessageData_ofFormat(v___x_1925_);
v___x_1927_ = l_Lean_addTrace___redArg(v_inst_1917_, v_inst_1918_, v_toMonadRef_1919_, v_inst_1920_, v_fst_1921_, v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__2___boxed(lean_object* v_toPure_1928_, lean_object* v_snd_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_toMonadRef_1932_, lean_object* v_inst_1933_, lean_object* v_fst_1934_, lean_object* v_____do__lift_1935_){
_start:
{
uint8_t v_____do__lift_1444__boxed_1936_; lean_object* v_res_1937_; 
v_____do__lift_1444__boxed_1936_ = lean_unbox(v_____do__lift_1935_);
v_res_1937_ = l_Lean_Elab_liftMacroM___redArg___lam__2(v_toPure_1928_, v_snd_1929_, v_inst_1930_, v_inst_1931_, v_toMonadRef_1932_, v_inst_1933_, v_fst_1934_, v_____do__lift_1444__boxed_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__3(lean_object* v_inst_1938_, lean_object* v_toPure_1939_, lean_object* v_toBind_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_toMonadRef_1943_, lean_object* v_inst_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v_getInheritedTraceOptions_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_fst_1946_ = lean_ctor_get(v_x_1945_, 0);
lean_inc_n(v_fst_1946_, 2);
v_snd_1947_ = lean_ctor_get(v_x_1945_, 1);
lean_inc(v_snd_1947_);
lean_dec_ref(v_x_1945_);
v_getInheritedTraceOptions_1948_ = lean_ctor_get(v_inst_1938_, 2);
lean_inc(v_getInheritedTraceOptions_1948_);
lean_inc_n(v_toBind_1940_, 2);
lean_inc(v_toPure_1939_);
v___f_1949_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1949_, 0, v_toPure_1939_);
lean_closure_set(v___f_1949_, 1, v_fst_1946_);
lean_closure_set(v___f_1949_, 2, v_toBind_1940_);
lean_closure_set(v___f_1949_, 3, v_inst_1941_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1950_, 0, v_toPure_1939_);
lean_closure_set(v___f_1950_, 1, v_snd_1947_);
lean_closure_set(v___f_1950_, 2, v_inst_1942_);
lean_closure_set(v___f_1950_, 3, v_inst_1938_);
lean_closure_set(v___f_1950_, 4, v_toMonadRef_1943_);
lean_closure_set(v___f_1950_, 5, v_inst_1944_);
lean_closure_set(v___f_1950_, 6, v_fst_1946_);
v___x_1951_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1948_, v___f_1949_);
v___x_1952_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v___x_1951_, v___f_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4(lean_object* v_env_1953_, lean_object* v___x_1954_, lean_object* v___x_1955_, lean_object* v_stx_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1953_, v_stx_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
if (lean_obj_tag(v_a_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___x_1955_);
lean_dec_ref(v___x_1954_);
v_a_1961_ = lean_ctor_get(v___x_1959_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1970_);
v___x_1963_ = v___x_1959_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_box(0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1961_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_val_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2001_; 
v_val_1971_ = lean_ctor_get(v_a_1960_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_a_1960_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1973_ = v_a_1960_;
v_isShared_1974_ = v_isSharedCheck_2001_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_val_1971_);
lean_dec(v_a_1960_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2001_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_snd_1975_; 
v_snd_1975_ = lean_ctor_get(v_val_1971_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_val_1971_);
if (lean_obj_tag(v_snd_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1986_; 
lean_del_object(v___x_1973_);
v_a_1976_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1959_, 2);
v_a_1977_ = lean_ctor_get(v_snd_1975_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_snd_1975_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1979_ = v_snd_1975_;
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v_snd_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1186__overap_1983_; lean_object* v___x_1984_; 
v___x_1186__overap_1983_ = l_liftExcept___redArg(v___x_1954_, v___x_1955_, v___x_1982_);
lean_inc_ref(v___y_1957_);
v___x_1984_ = lean_apply_2(v___x_1186__overap_1983_, v___y_1957_, v_a_1976_);
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2000_; 
v_a_1987_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1959_, 2);
v_a_1988_ = lean_ctor_get(v_snd_1975_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_snd_1975_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1990_ = v_snd_1975_;
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v_snd_1975_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_a_1988_);
v___x_1993_ = v___x_1973_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1190__overap_1996_; lean_object* v___x_1997_; 
v___x_1190__overap_1996_ = l_liftExcept___redArg(v___x_1954_, v___x_1955_, v___x_1995_);
lean_inc_ref(v___y_1957_);
v___x_1997_ = lean_apply_2(v___x_1190__overap_1996_, v___y_1957_, v_a_1987_);
return v___x_1997_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v___x_1955_);
lean_dec_ref(v___x_1954_);
v_a_2002_ = lean_ctor_get(v___x_1959_, 0);
v_a_2003_ = lean_ctor_get(v___x_1959_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1959_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_inc(v_a_2002_);
lean_dec(v___x_1959_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
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
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(lean_object* v_env_2011_, lean_object* v___x_2012_, lean_object* v___x_2013_, lean_object* v_stx_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Elab_liftMacroM___redArg___lam__4(v_env_2011_, v___x_2012_, v___x_2013_, v_stx_2014_, v___y_2015_, v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5(lean_object* v_env_2018_, lean_object* v_declName_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2022_; lean_object* v_env_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2022_ = 0;
v_env_2023_ = l_Lean_Environment_setExporting(v_env_2018_, v___x_2022_);
lean_inc(v_declName_2019_);
v___x_2024_ = l_Lean_mkPrivateName(v_env_2023_, v_declName_2019_);
v___x_2025_ = 1;
lean_inc_ref(v_env_2023_);
v___x_2026_ = l_Lean_Environment_contains(v_env_2023_, v___x_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = l_Lean_privateToUserName(v_declName_2019_);
v___x_2028_ = l_Lean_Environment_contains(v_env_2023_, v___x_2027_, v___x_2025_);
v___x_2029_ = lean_box(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___y_2021_);
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v_env_2023_);
lean_dec(v_declName_2019_);
v___x_2031_ = lean_box(v___x_2026_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___y_2021_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(lean_object* v_env_2033_, lean_object* v_declName_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_liftMacroM___redArg___lam__5(v_env_2033_, v_declName_2034_, v___y_2035_, v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6(lean_object* v_env_2038_, lean_object* v_currNamespace_2039_, lean_object* v_openDecls_2040_, lean_object* v_n_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = l_Lean_ResolveName_resolveNamespace(v_env_2038_, v_currNamespace_2039_, v_openDecls_2040_, v_n_2041_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___y_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(lean_object* v_env_2046_, lean_object* v_currNamespace_2047_, lean_object* v_openDecls_2048_, lean_object* v_n_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_liftMacroM___redArg___lam__6(v_env_2046_, v_currNamespace_2047_, v_openDecls_2048_, v_n_2049_, v___y_2050_, v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7(lean_object* v_env_2053_, lean_object* v_opts_2054_, lean_object* v_currNamespace_2055_, lean_object* v_openDecls_2056_, lean_object* v_n_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = l_Lean_ResolveName_resolveGlobalName(v_env_2053_, v_opts_2054_, v_currNamespace_2055_, v_openDecls_2056_, v_n_2057_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(lean_object* v_env_2062_, lean_object* v_opts_2063_, lean_object* v_currNamespace_2064_, lean_object* v_openDecls_2065_, lean_object* v_n_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_liftMacroM___redArg___lam__7(v_env_2062_, v_opts_2063_, v_currNamespace_2064_, v_openDecls_2065_, v_n_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec_ref(v_opts_2063_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__8(lean_object* v_toPure_2070_, lean_object* v_a_2071_, lean_object* v_____r_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_apply_2(v_toPure_2070_, lean_box(0), v_a_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__9(lean_object* v_traceMsgs_2074_, lean_object* v_inst_2075_, lean_object* v___f_2076_, lean_object* v_toBind_2077_, lean_object* v___f_2078_, lean_object* v_____r_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = l_List_reverse___redArg(v_traceMsgs_2074_);
v___x_2081_ = l_List_forM___redArg(v_inst_2075_, v___x_2080_, v___f_2076_);
v___x_2082_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2081_, v___f_2078_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__10(lean_object* v_setNextMacroScope_2083_, lean_object* v_macroScope_2084_, lean_object* v_toBind_2085_, lean_object* v___f_2086_, lean_object* v_____s_2087_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_apply_1(v_setNextMacroScope_2083_, v_macroScope_2084_);
v___x_2089_ = lean_apply_4(v_toBind_2085_, lean_box(0), lean_box(0), v___x_2088_, v___f_2086_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__11(lean_object* v___x_2090_, lean_object* v_toPure_2091_, lean_object* v_____r_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2090_);
v___x_2094_ = lean_apply_2(v_toPure_2091_, lean_box(0), v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__12(lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_toMonadRef_2099_, lean_object* v_inst_2100_, lean_object* v_toBind_2101_, lean_object* v___f_2102_, lean_object* v_a_2103_, lean_object* v_x_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = 1;
v___x_2107_ = l_Lean_recordExtraModUseFromDecl___redArg(v_inst_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_toMonadRef_2099_, v_inst_2100_, v_a_2103_, v___x_2106_);
v___x_2108_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2107_, v___f_2102_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13(lean_object* v_methods_2110_, lean_object* v_____do__lift_2111_, lean_object* v_____do__lift_2112_, lean_object* v_____do__lift_2113_, lean_object* v_____do__lift_2114_, lean_object* v_____do__lift_2115_, lean_object* v_x_2116_, lean_object* v_toPure_2117_, lean_object* v_inst_2118_, lean_object* v___f_2119_, lean_object* v_toBind_2120_, lean_object* v_setNextMacroScope_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_toMonadRef_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_toMonadExceptOf_2128_, lean_object* v_____do__lift_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2130_, 0, v_methods_2110_);
lean_ctor_set(v___x_2130_, 1, v_____do__lift_2111_);
lean_ctor_set(v___x_2130_, 2, v_____do__lift_2112_);
lean_ctor_set(v___x_2130_, 3, v_____do__lift_2113_);
lean_ctor_set(v___x_2130_, 4, v_____do__lift_2114_);
lean_ctor_set(v___x_2130_, 5, v_____do__lift_2115_);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2132_, 0, v_____do__lift_2129_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
lean_ctor_set(v___x_2132_, 2, v___x_2131_);
v___x_2133_ = lean_apply_2(v_x_2116_, v___x_2130_, v___x_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_a_2135_; lean_object* v_macroScope_2136_; lean_object* v_traceMsgs_2137_; lean_object* v_expandedMacroDecls_2138_; lean_object* v___f_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v_toMonadExceptOf_2128_);
lean_dec_ref(v_inst_2127_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 1);
lean_inc(v_a_2134_);
v_a_2135_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2133_, 2);
v_macroScope_2136_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_macroScope_2136_);
v_traceMsgs_2137_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_traceMsgs_2137_);
v_expandedMacroDecls_2138_ = lean_ctor_get(v_a_2134_, 2);
lean_inc(v_expandedMacroDecls_2138_);
lean_dec(v_a_2134_);
lean_inc(v_toPure_2117_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2139_, 0, v_toPure_2117_);
lean_closure_set(v___f_2139_, 1, v_a_2135_);
lean_inc_n(v_toBind_2120_, 3);
lean_inc_ref_n(v_inst_2118_, 2);
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__9), 6, 5);
lean_closure_set(v___f_2140_, 0, v_traceMsgs_2137_);
lean_closure_set(v___f_2140_, 1, v_inst_2118_);
lean_closure_set(v___f_2140_, 2, v___f_2119_);
lean_closure_set(v___f_2140_, 3, v_toBind_2120_);
lean_closure_set(v___f_2140_, 4, v___f_2139_);
v___f_2141_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2141_, 0, v_setNextMacroScope_2121_);
lean_closure_set(v___f_2141_, 1, v_macroScope_2136_);
lean_closure_set(v___f_2141_, 2, v_toBind_2120_);
lean_closure_set(v___f_2141_, 3, v___f_2140_);
v___x_2142_ = lean_box(0);
v___f_2143_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2143_, 0, v___x_2142_);
lean_closure_set(v___f_2143_, 1, v_toPure_2117_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__12), 11, 8);
lean_closure_set(v___f_2144_, 0, v_inst_2118_);
lean_closure_set(v___f_2144_, 1, v_inst_2122_);
lean_closure_set(v___f_2144_, 2, v_inst_2123_);
lean_closure_set(v___f_2144_, 3, v_inst_2124_);
lean_closure_set(v___f_2144_, 4, v_toMonadRef_2125_);
lean_closure_set(v___f_2144_, 5, v_inst_2126_);
lean_closure_set(v___f_2144_, 6, v_toBind_2120_);
lean_closure_set(v___f_2144_, 7, v___f_2143_);
v___x_2145_ = l_List_forIn_x27_loop___redArg(v_inst_2118_, v___f_2144_, v_expandedMacroDecls_2138_, v___x_2142_);
lean_dec(v_expandedMacroDecls_2138_);
v___x_2146_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v___x_2145_, v___f_2141_);
return v___x_2146_;
}
else
{
lean_object* v_a_2147_; 
lean_dec(v_inst_2126_);
lean_dec_ref(v_toMonadRef_2125_);
lean_dec(v_inst_2124_);
lean_dec_ref(v_inst_2123_);
lean_dec_ref(v_inst_2122_);
lean_dec(v_setNextMacroScope_2121_);
lean_dec(v_toBind_2120_);
lean_dec(v___f_2119_);
lean_dec(v_toPure_2117_);
v_a_2147_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2133_, 2);
if (lean_obj_tag(v_a_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_a_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
lean_dec_ref(v_toMonadExceptOf_2128_);
v_a_2148_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_a_2148_);
v_a_2149_ = lean_ctor_get(v_a_2147_, 1);
lean_inc_ref(v_a_2149_);
lean_dec_ref_known(v_a_2147_, 2);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0));
v___x_2151_ = lean_string_dec_eq(v_a_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_a_2149_);
v___x_2153_ = l_Lean_MessageData_ofFormat(v___x_2152_);
v___x_2154_ = l_Lean_throwErrorAt___redArg(v_inst_2118_, v_inst_2127_, v_a_2148_, v___x_2153_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; 
lean_dec_ref(v_a_2149_);
lean_dec_ref(v_inst_2118_);
v___x_2155_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_2127_, v_a_2148_);
return v___x_2155_;
}
}
else
{
lean_object* v___x_2156_; 
lean_dec_ref(v_inst_2127_);
lean_dec_ref(v_inst_2118_);
v___x_2156_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_2128_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_methods_2157_ = _args[0];
lean_object* v_____do__lift_2158_ = _args[1];
lean_object* v_____do__lift_2159_ = _args[2];
lean_object* v_____do__lift_2160_ = _args[3];
lean_object* v_____do__lift_2161_ = _args[4];
lean_object* v_____do__lift_2162_ = _args[5];
lean_object* v_x_2163_ = _args[6];
lean_object* v_toPure_2164_ = _args[7];
lean_object* v_inst_2165_ = _args[8];
lean_object* v___f_2166_ = _args[9];
lean_object* v_toBind_2167_ = _args[10];
lean_object* v_setNextMacroScope_2168_ = _args[11];
lean_object* v_inst_2169_ = _args[12];
lean_object* v_inst_2170_ = _args[13];
lean_object* v_inst_2171_ = _args[14];
lean_object* v_toMonadRef_2172_ = _args[15];
lean_object* v_inst_2173_ = _args[16];
lean_object* v_inst_2174_ = _args[17];
lean_object* v_toMonadExceptOf_2175_ = _args[18];
lean_object* v_____do__lift_2176_ = _args[19];
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Elab_liftMacroM___redArg___lam__13(v_methods_2157_, v_____do__lift_2158_, v_____do__lift_2159_, v_____do__lift_2160_, v_____do__lift_2161_, v_____do__lift_2162_, v_x_2163_, v_toPure_2164_, v_inst_2165_, v___f_2166_, v_toBind_2167_, v_setNextMacroScope_2168_, v_inst_2169_, v_inst_2170_, v_inst_2171_, v_toMonadRef_2172_, v_inst_2173_, v_inst_2174_, v_toMonadExceptOf_2175_, v_____do__lift_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14(lean_object* v_methods_2178_, lean_object* v_____do__lift_2179_, lean_object* v_____do__lift_2180_, lean_object* v_____do__lift_2181_, lean_object* v_____do__lift_2182_, lean_object* v_x_2183_, lean_object* v_toPure_2184_, lean_object* v_inst_2185_, lean_object* v___f_2186_, lean_object* v_toBind_2187_, lean_object* v_setNextMacroScope_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_toMonadRef_2192_, lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_toMonadExceptOf_2195_, lean_object* v_getNextMacroScope_2196_, lean_object* v_____do__lift_2197_){
_start:
{
lean_object* v___f_2198_; lean_object* v___x_2199_; 
lean_inc(v_toBind_2187_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__13___boxed), 20, 19);
lean_closure_set(v___f_2198_, 0, v_methods_2178_);
lean_closure_set(v___f_2198_, 1, v_____do__lift_2179_);
lean_closure_set(v___f_2198_, 2, v_____do__lift_2180_);
lean_closure_set(v___f_2198_, 3, v_____do__lift_2181_);
lean_closure_set(v___f_2198_, 4, v_____do__lift_2197_);
lean_closure_set(v___f_2198_, 5, v_____do__lift_2182_);
lean_closure_set(v___f_2198_, 6, v_x_2183_);
lean_closure_set(v___f_2198_, 7, v_toPure_2184_);
lean_closure_set(v___f_2198_, 8, v_inst_2185_);
lean_closure_set(v___f_2198_, 9, v___f_2186_);
lean_closure_set(v___f_2198_, 10, v_toBind_2187_);
lean_closure_set(v___f_2198_, 11, v_setNextMacroScope_2188_);
lean_closure_set(v___f_2198_, 12, v_inst_2189_);
lean_closure_set(v___f_2198_, 13, v_inst_2190_);
lean_closure_set(v___f_2198_, 14, v_inst_2191_);
lean_closure_set(v___f_2198_, 15, v_toMonadRef_2192_);
lean_closure_set(v___f_2198_, 16, v_inst_2193_);
lean_closure_set(v___f_2198_, 17, v_inst_2194_);
lean_closure_set(v___f_2198_, 18, v_toMonadExceptOf_2195_);
v___x_2199_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v_getNextMacroScope_2196_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_methods_2200_ = _args[0];
lean_object* v_____do__lift_2201_ = _args[1];
lean_object* v_____do__lift_2202_ = _args[2];
lean_object* v_____do__lift_2203_ = _args[3];
lean_object* v_____do__lift_2204_ = _args[4];
lean_object* v_x_2205_ = _args[5];
lean_object* v_toPure_2206_ = _args[6];
lean_object* v_inst_2207_ = _args[7];
lean_object* v___f_2208_ = _args[8];
lean_object* v_toBind_2209_ = _args[9];
lean_object* v_setNextMacroScope_2210_ = _args[10];
lean_object* v_inst_2211_ = _args[11];
lean_object* v_inst_2212_ = _args[12];
lean_object* v_inst_2213_ = _args[13];
lean_object* v_toMonadRef_2214_ = _args[14];
lean_object* v_inst_2215_ = _args[15];
lean_object* v_inst_2216_ = _args[16];
lean_object* v_toMonadExceptOf_2217_ = _args[17];
lean_object* v_getNextMacroScope_2218_ = _args[18];
lean_object* v_____do__lift_2219_ = _args[19];
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_liftMacroM___redArg___lam__14(v_methods_2200_, v_____do__lift_2201_, v_____do__lift_2202_, v_____do__lift_2203_, v_____do__lift_2204_, v_x_2205_, v_toPure_2206_, v_inst_2207_, v___f_2208_, v_toBind_2209_, v_setNextMacroScope_2210_, v_inst_2211_, v_inst_2212_, v_inst_2213_, v_toMonadRef_2214_, v_inst_2215_, v_inst_2216_, v_toMonadExceptOf_2217_, v_getNextMacroScope_2218_, v_____do__lift_2219_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15(lean_object* v_methods_2221_, lean_object* v_____do__lift_2222_, lean_object* v_____do__lift_2223_, lean_object* v_____do__lift_2224_, lean_object* v_x_2225_, lean_object* v_toPure_2226_, lean_object* v_inst_2227_, lean_object* v___f_2228_, lean_object* v_toBind_2229_, lean_object* v_setNextMacroScope_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_toMonadRef_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_toMonadExceptOf_2237_, lean_object* v_getNextMacroScope_2238_, lean_object* v_getMaxRecDepth_2239_, lean_object* v_____do__lift_2240_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; 
lean_inc(v_toBind_2229_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__14___boxed), 20, 19);
lean_closure_set(v___f_2241_, 0, v_methods_2221_);
lean_closure_set(v___f_2241_, 1, v_____do__lift_2222_);
lean_closure_set(v___f_2241_, 2, v_____do__lift_2223_);
lean_closure_set(v___f_2241_, 3, v_____do__lift_2240_);
lean_closure_set(v___f_2241_, 4, v_____do__lift_2224_);
lean_closure_set(v___f_2241_, 5, v_x_2225_);
lean_closure_set(v___f_2241_, 6, v_toPure_2226_);
lean_closure_set(v___f_2241_, 7, v_inst_2227_);
lean_closure_set(v___f_2241_, 8, v___f_2228_);
lean_closure_set(v___f_2241_, 9, v_toBind_2229_);
lean_closure_set(v___f_2241_, 10, v_setNextMacroScope_2230_);
lean_closure_set(v___f_2241_, 11, v_inst_2231_);
lean_closure_set(v___f_2241_, 12, v_inst_2232_);
lean_closure_set(v___f_2241_, 13, v_inst_2233_);
lean_closure_set(v___f_2241_, 14, v_toMonadRef_2234_);
lean_closure_set(v___f_2241_, 15, v_inst_2235_);
lean_closure_set(v___f_2241_, 16, v_inst_2236_);
lean_closure_set(v___f_2241_, 17, v_toMonadExceptOf_2237_);
lean_closure_set(v___f_2241_, 18, v_getNextMacroScope_2238_);
v___x_2242_ = lean_apply_4(v_toBind_2229_, lean_box(0), lean_box(0), v_getMaxRecDepth_2239_, v___f_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_methods_2243_ = _args[0];
lean_object* v_____do__lift_2244_ = _args[1];
lean_object* v_____do__lift_2245_ = _args[2];
lean_object* v_____do__lift_2246_ = _args[3];
lean_object* v_x_2247_ = _args[4];
lean_object* v_toPure_2248_ = _args[5];
lean_object* v_inst_2249_ = _args[6];
lean_object* v___f_2250_ = _args[7];
lean_object* v_toBind_2251_ = _args[8];
lean_object* v_setNextMacroScope_2252_ = _args[9];
lean_object* v_inst_2253_ = _args[10];
lean_object* v_inst_2254_ = _args[11];
lean_object* v_inst_2255_ = _args[12];
lean_object* v_toMonadRef_2256_ = _args[13];
lean_object* v_inst_2257_ = _args[14];
lean_object* v_inst_2258_ = _args[15];
lean_object* v_toMonadExceptOf_2259_ = _args[16];
lean_object* v_getNextMacroScope_2260_ = _args[17];
lean_object* v_getMaxRecDepth_2261_ = _args[18];
lean_object* v_____do__lift_2262_ = _args[19];
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Elab_liftMacroM___redArg___lam__15(v_methods_2243_, v_____do__lift_2244_, v_____do__lift_2245_, v_____do__lift_2246_, v_x_2247_, v_toPure_2248_, v_inst_2249_, v___f_2250_, v_toBind_2251_, v_setNextMacroScope_2252_, v_inst_2253_, v_inst_2254_, v_inst_2255_, v_toMonadRef_2256_, v_inst_2257_, v_inst_2258_, v_toMonadExceptOf_2259_, v_getNextMacroScope_2260_, v_getMaxRecDepth_2261_, v_____do__lift_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16(lean_object* v_inst_2264_, lean_object* v_methods_2265_, lean_object* v_____do__lift_2266_, lean_object* v_____do__lift_2267_, lean_object* v_x_2268_, lean_object* v_toPure_2269_, lean_object* v_inst_2270_, lean_object* v___f_2271_, lean_object* v_toBind_2272_, lean_object* v_setNextMacroScope_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_toMonadRef_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_toMonadExceptOf_2280_, lean_object* v_getNextMacroScope_2281_, lean_object* v_____do__lift_2282_){
_start:
{
lean_object* v_getRecDepth_2283_; lean_object* v_getMaxRecDepth_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; 
v_getRecDepth_2283_ = lean_ctor_get(v_inst_2264_, 1);
lean_inc(v_getRecDepth_2283_);
v_getMaxRecDepth_2284_ = lean_ctor_get(v_inst_2264_, 2);
lean_inc(v_getMaxRecDepth_2284_);
lean_dec_ref(v_inst_2264_);
lean_inc(v_toBind_2272_);
v___f_2285_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_2285_, 0, v_methods_2265_);
lean_closure_set(v___f_2285_, 1, v_____do__lift_2282_);
lean_closure_set(v___f_2285_, 2, v_____do__lift_2266_);
lean_closure_set(v___f_2285_, 3, v_____do__lift_2267_);
lean_closure_set(v___f_2285_, 4, v_x_2268_);
lean_closure_set(v___f_2285_, 5, v_toPure_2269_);
lean_closure_set(v___f_2285_, 6, v_inst_2270_);
lean_closure_set(v___f_2285_, 7, v___f_2271_);
lean_closure_set(v___f_2285_, 8, v_toBind_2272_);
lean_closure_set(v___f_2285_, 9, v_setNextMacroScope_2273_);
lean_closure_set(v___f_2285_, 10, v_inst_2274_);
lean_closure_set(v___f_2285_, 11, v_inst_2275_);
lean_closure_set(v___f_2285_, 12, v_inst_2276_);
lean_closure_set(v___f_2285_, 13, v_toMonadRef_2277_);
lean_closure_set(v___f_2285_, 14, v_inst_2278_);
lean_closure_set(v___f_2285_, 15, v_inst_2279_);
lean_closure_set(v___f_2285_, 16, v_toMonadExceptOf_2280_);
lean_closure_set(v___f_2285_, 17, v_getNextMacroScope_2281_);
lean_closure_set(v___f_2285_, 18, v_getMaxRecDepth_2284_);
v___x_2286_ = lean_apply_4(v_toBind_2272_, lean_box(0), lean_box(0), v_getRecDepth_2283_, v___f_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_2287_ = _args[0];
lean_object* v_methods_2288_ = _args[1];
lean_object* v_____do__lift_2289_ = _args[2];
lean_object* v_____do__lift_2290_ = _args[3];
lean_object* v_x_2291_ = _args[4];
lean_object* v_toPure_2292_ = _args[5];
lean_object* v_inst_2293_ = _args[6];
lean_object* v___f_2294_ = _args[7];
lean_object* v_toBind_2295_ = _args[8];
lean_object* v_setNextMacroScope_2296_ = _args[9];
lean_object* v_inst_2297_ = _args[10];
lean_object* v_inst_2298_ = _args[11];
lean_object* v_inst_2299_ = _args[12];
lean_object* v_toMonadRef_2300_ = _args[13];
lean_object* v_inst_2301_ = _args[14];
lean_object* v_inst_2302_ = _args[15];
lean_object* v_toMonadExceptOf_2303_ = _args[16];
lean_object* v_getNextMacroScope_2304_ = _args[17];
lean_object* v_____do__lift_2305_ = _args[18];
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Elab_liftMacroM___redArg___lam__16(v_inst_2287_, v_methods_2288_, v_____do__lift_2289_, v_____do__lift_2290_, v_x_2291_, v_toPure_2292_, v_inst_2293_, v___f_2294_, v_toBind_2295_, v_setNextMacroScope_2296_, v_inst_2297_, v_inst_2298_, v_inst_2299_, v_toMonadRef_2300_, v_inst_2301_, v_inst_2302_, v_toMonadExceptOf_2303_, v_getNextMacroScope_2304_, v_____do__lift_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17(lean_object* v_inst_2307_, lean_object* v_methods_2308_, lean_object* v_____do__lift_2309_, lean_object* v_x_2310_, lean_object* v_toPure_2311_, lean_object* v_inst_2312_, lean_object* v___f_2313_, lean_object* v_toBind_2314_, lean_object* v_setNextMacroScope_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_toMonadRef_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_toMonadExceptOf_2322_, lean_object* v_getNextMacroScope_2323_, lean_object* v_getContext_2324_, lean_object* v_____do__lift_2325_){
_start:
{
lean_object* v___f_2326_; lean_object* v___x_2327_; 
lean_inc(v_toBind_2314_);
v___f_2326_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__16___boxed), 19, 18);
lean_closure_set(v___f_2326_, 0, v_inst_2307_);
lean_closure_set(v___f_2326_, 1, v_methods_2308_);
lean_closure_set(v___f_2326_, 2, v_____do__lift_2325_);
lean_closure_set(v___f_2326_, 3, v_____do__lift_2309_);
lean_closure_set(v___f_2326_, 4, v_x_2310_);
lean_closure_set(v___f_2326_, 5, v_toPure_2311_);
lean_closure_set(v___f_2326_, 6, v_inst_2312_);
lean_closure_set(v___f_2326_, 7, v___f_2313_);
lean_closure_set(v___f_2326_, 8, v_toBind_2314_);
lean_closure_set(v___f_2326_, 9, v_setNextMacroScope_2315_);
lean_closure_set(v___f_2326_, 10, v_inst_2316_);
lean_closure_set(v___f_2326_, 11, v_inst_2317_);
lean_closure_set(v___f_2326_, 12, v_inst_2318_);
lean_closure_set(v___f_2326_, 13, v_toMonadRef_2319_);
lean_closure_set(v___f_2326_, 14, v_inst_2320_);
lean_closure_set(v___f_2326_, 15, v_inst_2321_);
lean_closure_set(v___f_2326_, 16, v_toMonadExceptOf_2322_);
lean_closure_set(v___f_2326_, 17, v_getNextMacroScope_2323_);
v___x_2327_ = lean_apply_4(v_toBind_2314_, lean_box(0), lean_box(0), v_getContext_2324_, v___f_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_2328_ = _args[0];
lean_object* v_methods_2329_ = _args[1];
lean_object* v_____do__lift_2330_ = _args[2];
lean_object* v_x_2331_ = _args[3];
lean_object* v_toPure_2332_ = _args[4];
lean_object* v_inst_2333_ = _args[5];
lean_object* v___f_2334_ = _args[6];
lean_object* v_toBind_2335_ = _args[7];
lean_object* v_setNextMacroScope_2336_ = _args[8];
lean_object* v_inst_2337_ = _args[9];
lean_object* v_inst_2338_ = _args[10];
lean_object* v_inst_2339_ = _args[11];
lean_object* v_toMonadRef_2340_ = _args[12];
lean_object* v_inst_2341_ = _args[13];
lean_object* v_inst_2342_ = _args[14];
lean_object* v_toMonadExceptOf_2343_ = _args[15];
lean_object* v_getNextMacroScope_2344_ = _args[16];
lean_object* v_getContext_2345_ = _args[17];
lean_object* v_____do__lift_2346_ = _args[18];
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Elab_liftMacroM___redArg___lam__17(v_inst_2328_, v_methods_2329_, v_____do__lift_2330_, v_x_2331_, v_toPure_2332_, v_inst_2333_, v___f_2334_, v_toBind_2335_, v_setNextMacroScope_2336_, v_inst_2337_, v_inst_2338_, v_inst_2339_, v_toMonadRef_2340_, v_inst_2341_, v_inst_2342_, v_toMonadExceptOf_2343_, v_getNextMacroScope_2344_, v_getContext_2345_, v_____do__lift_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18(lean_object* v_toMonadQuotation_2348_, lean_object* v_inst_2349_, lean_object* v_methods_2350_, lean_object* v_x_2351_, lean_object* v_toPure_2352_, lean_object* v_inst_2353_, lean_object* v___f_2354_, lean_object* v_toBind_2355_, lean_object* v_setNextMacroScope_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_toMonadRef_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_toMonadExceptOf_2363_, lean_object* v_getNextMacroScope_2364_, lean_object* v_____do__lift_2365_){
_start:
{
lean_object* v_getCurrMacroScope_2366_; lean_object* v_getContext_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v_getCurrMacroScope_2366_ = lean_ctor_get(v_toMonadQuotation_2348_, 1);
lean_inc(v_getCurrMacroScope_2366_);
v_getContext_2367_ = lean_ctor_get(v_toMonadQuotation_2348_, 2);
lean_inc(v_getContext_2367_);
lean_dec_ref(v_toMonadQuotation_2348_);
lean_inc(v_toBind_2355_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__17___boxed), 19, 18);
lean_closure_set(v___f_2368_, 0, v_inst_2349_);
lean_closure_set(v___f_2368_, 1, v_methods_2350_);
lean_closure_set(v___f_2368_, 2, v_____do__lift_2365_);
lean_closure_set(v___f_2368_, 3, v_x_2351_);
lean_closure_set(v___f_2368_, 4, v_toPure_2352_);
lean_closure_set(v___f_2368_, 5, v_inst_2353_);
lean_closure_set(v___f_2368_, 6, v___f_2354_);
lean_closure_set(v___f_2368_, 7, v_toBind_2355_);
lean_closure_set(v___f_2368_, 8, v_setNextMacroScope_2356_);
lean_closure_set(v___f_2368_, 9, v_inst_2357_);
lean_closure_set(v___f_2368_, 10, v_inst_2358_);
lean_closure_set(v___f_2368_, 11, v_inst_2359_);
lean_closure_set(v___f_2368_, 12, v_toMonadRef_2360_);
lean_closure_set(v___f_2368_, 13, v_inst_2361_);
lean_closure_set(v___f_2368_, 14, v_inst_2362_);
lean_closure_set(v___f_2368_, 15, v_toMonadExceptOf_2363_);
lean_closure_set(v___f_2368_, 16, v_getNextMacroScope_2364_);
lean_closure_set(v___f_2368_, 17, v_getContext_2367_);
v___x_2369_ = lean_apply_4(v_toBind_2355_, lean_box(0), lean_box(0), v_getCurrMacroScope_2366_, v___f_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_toMonadQuotation_2370_ = _args[0];
lean_object* v_inst_2371_ = _args[1];
lean_object* v_methods_2372_ = _args[2];
lean_object* v_x_2373_ = _args[3];
lean_object* v_toPure_2374_ = _args[4];
lean_object* v_inst_2375_ = _args[5];
lean_object* v___f_2376_ = _args[6];
lean_object* v_toBind_2377_ = _args[7];
lean_object* v_setNextMacroScope_2378_ = _args[8];
lean_object* v_inst_2379_ = _args[9];
lean_object* v_inst_2380_ = _args[10];
lean_object* v_inst_2381_ = _args[11];
lean_object* v_toMonadRef_2382_ = _args[12];
lean_object* v_inst_2383_ = _args[13];
lean_object* v_inst_2384_ = _args[14];
lean_object* v_toMonadExceptOf_2385_ = _args[15];
lean_object* v_getNextMacroScope_2386_ = _args[16];
lean_object* v_____do__lift_2387_ = _args[17];
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Elab_liftMacroM___redArg___lam__18(v_toMonadQuotation_2370_, v_inst_2371_, v_methods_2372_, v_x_2373_, v_toPure_2374_, v_inst_2375_, v___f_2376_, v_toBind_2377_, v_setNextMacroScope_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_toMonadRef_2382_, v_inst_2383_, v_inst_2384_, v_toMonadExceptOf_2385_, v_getNextMacroScope_2386_, v_____do__lift_2387_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19(lean_object* v_toMonadRef_2389_, lean_object* v_env_2390_, lean_object* v_currNamespace_2391_, lean_object* v_opts_2392_, lean_object* v___x_2393_, lean_object* v___f_2394_, lean_object* v___f_2395_, lean_object* v_toMonadQuotation_2396_, lean_object* v_inst_2397_, lean_object* v_x_2398_, lean_object* v_toPure_2399_, lean_object* v_inst_2400_, lean_object* v___f_2401_, lean_object* v_toBind_2402_, lean_object* v_setNextMacroScope_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_toMonadExceptOf_2409_, lean_object* v_getNextMacroScope_2410_, lean_object* v_openDecls_2411_){
_start:
{
lean_object* v_getRef_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; lean_object* v_methods_2416_; lean_object* v___f_2417_; lean_object* v___x_2418_; 
v_getRef_2412_ = lean_ctor_get(v_toMonadRef_2389_, 0);
lean_inc(v_getRef_2412_);
lean_inc(v_openDecls_2411_);
lean_inc_n(v_currNamespace_2391_, 2);
lean_inc_ref(v_env_2390_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__6___boxed), 6, 3);
lean_closure_set(v___f_2413_, 0, v_env_2390_);
lean_closure_set(v___f_2413_, 1, v_currNamespace_2391_);
lean_closure_set(v___f_2413_, 2, v_openDecls_2411_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2414_, 0, v_env_2390_);
lean_closure_set(v___f_2414_, 1, v_opts_2392_);
lean_closure_set(v___f_2414_, 2, v_currNamespace_2391_);
lean_closure_set(v___f_2414_, 3, v_openDecls_2411_);
v___x_2415_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(v___x_2415_, 0, lean_box(0));
lean_closure_set(v___x_2415_, 1, lean_box(0));
lean_closure_set(v___x_2415_, 2, v___x_2393_);
lean_closure_set(v___x_2415_, 3, lean_box(0));
lean_closure_set(v___x_2415_, 4, v_currNamespace_2391_);
v_methods_2416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2416_, 0, v___f_2394_);
lean_ctor_set(v_methods_2416_, 1, v___x_2415_);
lean_ctor_set(v_methods_2416_, 2, v___f_2395_);
lean_ctor_set(v_methods_2416_, 3, v___f_2413_);
lean_ctor_set(v_methods_2416_, 4, v___f_2414_);
lean_inc(v_toBind_2402_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__18___boxed), 18, 17);
lean_closure_set(v___f_2417_, 0, v_toMonadQuotation_2396_);
lean_closure_set(v___f_2417_, 1, v_inst_2397_);
lean_closure_set(v___f_2417_, 2, v_methods_2416_);
lean_closure_set(v___f_2417_, 3, v_x_2398_);
lean_closure_set(v___f_2417_, 4, v_toPure_2399_);
lean_closure_set(v___f_2417_, 5, v_inst_2400_);
lean_closure_set(v___f_2417_, 6, v___f_2401_);
lean_closure_set(v___f_2417_, 7, v_toBind_2402_);
lean_closure_set(v___f_2417_, 8, v_setNextMacroScope_2403_);
lean_closure_set(v___f_2417_, 9, v_inst_2404_);
lean_closure_set(v___f_2417_, 10, v_inst_2405_);
lean_closure_set(v___f_2417_, 11, v_inst_2406_);
lean_closure_set(v___f_2417_, 12, v_toMonadRef_2389_);
lean_closure_set(v___f_2417_, 13, v_inst_2407_);
lean_closure_set(v___f_2417_, 14, v_inst_2408_);
lean_closure_set(v___f_2417_, 15, v_toMonadExceptOf_2409_);
lean_closure_set(v___f_2417_, 16, v_getNextMacroScope_2410_);
v___x_2418_ = lean_apply_4(v_toBind_2402_, lean_box(0), lean_box(0), v_getRef_2412_, v___f_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_toMonadRef_2419_ = _args[0];
lean_object* v_env_2420_ = _args[1];
lean_object* v_currNamespace_2421_ = _args[2];
lean_object* v_opts_2422_ = _args[3];
lean_object* v___x_2423_ = _args[4];
lean_object* v___f_2424_ = _args[5];
lean_object* v___f_2425_ = _args[6];
lean_object* v_toMonadQuotation_2426_ = _args[7];
lean_object* v_inst_2427_ = _args[8];
lean_object* v_x_2428_ = _args[9];
lean_object* v_toPure_2429_ = _args[10];
lean_object* v_inst_2430_ = _args[11];
lean_object* v___f_2431_ = _args[12];
lean_object* v_toBind_2432_ = _args[13];
lean_object* v_setNextMacroScope_2433_ = _args[14];
lean_object* v_inst_2434_ = _args[15];
lean_object* v_inst_2435_ = _args[16];
lean_object* v_inst_2436_ = _args[17];
lean_object* v_inst_2437_ = _args[18];
lean_object* v_inst_2438_ = _args[19];
lean_object* v_toMonadExceptOf_2439_ = _args[20];
lean_object* v_getNextMacroScope_2440_ = _args[21];
lean_object* v_openDecls_2441_ = _args[22];
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Elab_liftMacroM___redArg___lam__19(v_toMonadRef_2419_, v_env_2420_, v_currNamespace_2421_, v_opts_2422_, v___x_2423_, v___f_2424_, v___f_2425_, v_toMonadQuotation_2426_, v_inst_2427_, v_x_2428_, v_toPure_2429_, v_inst_2430_, v___f_2431_, v_toBind_2432_, v_setNextMacroScope_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_, v_inst_2437_, v_inst_2438_, v_toMonadExceptOf_2439_, v_getNextMacroScope_2440_, v_openDecls_2441_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20(lean_object* v_toMonadRef_2443_, lean_object* v_env_2444_, lean_object* v_opts_2445_, lean_object* v___x_2446_, lean_object* v___f_2447_, lean_object* v___f_2448_, lean_object* v_toMonadQuotation_2449_, lean_object* v_inst_2450_, lean_object* v_x_2451_, lean_object* v_toPure_2452_, lean_object* v_inst_2453_, lean_object* v___f_2454_, lean_object* v_toBind_2455_, lean_object* v_setNextMacroScope_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_toMonadExceptOf_2462_, lean_object* v_getNextMacroScope_2463_, lean_object* v_getOpenDecls_2464_, lean_object* v_currNamespace_2465_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; 
lean_inc(v_toBind_2455_);
v___f_2466_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__19___boxed), 23, 22);
lean_closure_set(v___f_2466_, 0, v_toMonadRef_2443_);
lean_closure_set(v___f_2466_, 1, v_env_2444_);
lean_closure_set(v___f_2466_, 2, v_currNamespace_2465_);
lean_closure_set(v___f_2466_, 3, v_opts_2445_);
lean_closure_set(v___f_2466_, 4, v___x_2446_);
lean_closure_set(v___f_2466_, 5, v___f_2447_);
lean_closure_set(v___f_2466_, 6, v___f_2448_);
lean_closure_set(v___f_2466_, 7, v_toMonadQuotation_2449_);
lean_closure_set(v___f_2466_, 8, v_inst_2450_);
lean_closure_set(v___f_2466_, 9, v_x_2451_);
lean_closure_set(v___f_2466_, 10, v_toPure_2452_);
lean_closure_set(v___f_2466_, 11, v_inst_2453_);
lean_closure_set(v___f_2466_, 12, v___f_2454_);
lean_closure_set(v___f_2466_, 13, v_toBind_2455_);
lean_closure_set(v___f_2466_, 14, v_setNextMacroScope_2456_);
lean_closure_set(v___f_2466_, 15, v_inst_2457_);
lean_closure_set(v___f_2466_, 16, v_inst_2458_);
lean_closure_set(v___f_2466_, 17, v_inst_2459_);
lean_closure_set(v___f_2466_, 18, v_inst_2460_);
lean_closure_set(v___f_2466_, 19, v_inst_2461_);
lean_closure_set(v___f_2466_, 20, v_toMonadExceptOf_2462_);
lean_closure_set(v___f_2466_, 21, v_getNextMacroScope_2463_);
v___x_2467_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v_getOpenDecls_2464_, v___f_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_toMonadRef_2468_ = _args[0];
lean_object* v_env_2469_ = _args[1];
lean_object* v_opts_2470_ = _args[2];
lean_object* v___x_2471_ = _args[3];
lean_object* v___f_2472_ = _args[4];
lean_object* v___f_2473_ = _args[5];
lean_object* v_toMonadQuotation_2474_ = _args[6];
lean_object* v_inst_2475_ = _args[7];
lean_object* v_x_2476_ = _args[8];
lean_object* v_toPure_2477_ = _args[9];
lean_object* v_inst_2478_ = _args[10];
lean_object* v___f_2479_ = _args[11];
lean_object* v_toBind_2480_ = _args[12];
lean_object* v_setNextMacroScope_2481_ = _args[13];
lean_object* v_inst_2482_ = _args[14];
lean_object* v_inst_2483_ = _args[15];
lean_object* v_inst_2484_ = _args[16];
lean_object* v_inst_2485_ = _args[17];
lean_object* v_inst_2486_ = _args[18];
lean_object* v_toMonadExceptOf_2487_ = _args[19];
lean_object* v_getNextMacroScope_2488_ = _args[20];
lean_object* v_getOpenDecls_2489_ = _args[21];
lean_object* v_currNamespace_2490_ = _args[22];
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Elab_liftMacroM___redArg___lam__20(v_toMonadRef_2468_, v_env_2469_, v_opts_2470_, v___x_2471_, v___f_2472_, v___f_2473_, v_toMonadQuotation_2474_, v_inst_2475_, v_x_2476_, v_toPure_2477_, v_inst_2478_, v___f_2479_, v_toBind_2480_, v_setNextMacroScope_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_inst_2486_, v_toMonadExceptOf_2487_, v_getNextMacroScope_2488_, v_getOpenDecls_2489_, v_currNamespace_2490_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21(lean_object* v_inst_2492_, lean_object* v_toMonadRef_2493_, lean_object* v_env_2494_, lean_object* v___x_2495_, lean_object* v___f_2496_, lean_object* v___f_2497_, lean_object* v_toMonadQuotation_2498_, lean_object* v_inst_2499_, lean_object* v_x_2500_, lean_object* v_toPure_2501_, lean_object* v_inst_2502_, lean_object* v___f_2503_, lean_object* v_toBind_2504_, lean_object* v_setNextMacroScope_2505_, lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_toMonadExceptOf_2511_, lean_object* v_getNextMacroScope_2512_, lean_object* v_opts_2513_){
_start:
{
lean_object* v_getCurrNamespace_2514_; lean_object* v_getOpenDecls_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; 
v_getCurrNamespace_2514_ = lean_ctor_get(v_inst_2492_, 0);
lean_inc(v_getCurrNamespace_2514_);
v_getOpenDecls_2515_ = lean_ctor_get(v_inst_2492_, 1);
lean_inc(v_getOpenDecls_2515_);
lean_dec_ref(v_inst_2492_);
lean_inc(v_toBind_2504_);
v___f_2516_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__20___boxed), 23, 22);
lean_closure_set(v___f_2516_, 0, v_toMonadRef_2493_);
lean_closure_set(v___f_2516_, 1, v_env_2494_);
lean_closure_set(v___f_2516_, 2, v_opts_2513_);
lean_closure_set(v___f_2516_, 3, v___x_2495_);
lean_closure_set(v___f_2516_, 4, v___f_2496_);
lean_closure_set(v___f_2516_, 5, v___f_2497_);
lean_closure_set(v___f_2516_, 6, v_toMonadQuotation_2498_);
lean_closure_set(v___f_2516_, 7, v_inst_2499_);
lean_closure_set(v___f_2516_, 8, v_x_2500_);
lean_closure_set(v___f_2516_, 9, v_toPure_2501_);
lean_closure_set(v___f_2516_, 10, v_inst_2502_);
lean_closure_set(v___f_2516_, 11, v___f_2503_);
lean_closure_set(v___f_2516_, 12, v_toBind_2504_);
lean_closure_set(v___f_2516_, 13, v_setNextMacroScope_2505_);
lean_closure_set(v___f_2516_, 14, v_inst_2506_);
lean_closure_set(v___f_2516_, 15, v_inst_2507_);
lean_closure_set(v___f_2516_, 16, v_inst_2508_);
lean_closure_set(v___f_2516_, 17, v_inst_2509_);
lean_closure_set(v___f_2516_, 18, v_inst_2510_);
lean_closure_set(v___f_2516_, 19, v_toMonadExceptOf_2511_);
lean_closure_set(v___f_2516_, 20, v_getNextMacroScope_2512_);
lean_closure_set(v___f_2516_, 21, v_getOpenDecls_2515_);
v___x_2517_ = lean_apply_4(v_toBind_2504_, lean_box(0), lean_box(0), v_getCurrNamespace_2514_, v___f_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_inst_2518_ = _args[0];
lean_object* v_toMonadRef_2519_ = _args[1];
lean_object* v_env_2520_ = _args[2];
lean_object* v___x_2521_ = _args[3];
lean_object* v___f_2522_ = _args[4];
lean_object* v___f_2523_ = _args[5];
lean_object* v_toMonadQuotation_2524_ = _args[6];
lean_object* v_inst_2525_ = _args[7];
lean_object* v_x_2526_ = _args[8];
lean_object* v_toPure_2527_ = _args[9];
lean_object* v_inst_2528_ = _args[10];
lean_object* v___f_2529_ = _args[11];
lean_object* v_toBind_2530_ = _args[12];
lean_object* v_setNextMacroScope_2531_ = _args[13];
lean_object* v_inst_2532_ = _args[14];
lean_object* v_inst_2533_ = _args[15];
lean_object* v_inst_2534_ = _args[16];
lean_object* v_inst_2535_ = _args[17];
lean_object* v_inst_2536_ = _args[18];
lean_object* v_toMonadExceptOf_2537_ = _args[19];
lean_object* v_getNextMacroScope_2538_ = _args[20];
lean_object* v_opts_2539_ = _args[21];
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Elab_liftMacroM___redArg___lam__21(v_inst_2518_, v_toMonadRef_2519_, v_env_2520_, v___x_2521_, v___f_2522_, v___f_2523_, v_toMonadQuotation_2524_, v_inst_2525_, v_x_2526_, v_toPure_2527_, v_inst_2528_, v___f_2529_, v_toBind_2530_, v_setNextMacroScope_2531_, v_inst_2532_, v_inst_2533_, v_inst_2534_, v_inst_2535_, v_inst_2536_, v_toMonadExceptOf_2537_, v_getNextMacroScope_2538_, v_opts_2539_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22(lean_object* v___x_2541_, lean_object* v___x_2542_, lean_object* v_inst_2543_, lean_object* v_toMonadRef_2544_, lean_object* v___x_2545_, lean_object* v_toMonadQuotation_2546_, lean_object* v_inst_2547_, lean_object* v_x_2548_, lean_object* v_toPure_2549_, lean_object* v_inst_2550_, lean_object* v___f_2551_, lean_object* v_toBind_2552_, lean_object* v_setNextMacroScope_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_toMonadExceptOf_2559_, lean_object* v_getNextMacroScope_2560_, lean_object* v_env_2561_){
_start:
{
lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___x_2565_; 
lean_inc_ref_n(v_env_2561_, 2);
v___f_2562_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2562_, 0, v_env_2561_);
lean_closure_set(v___f_2562_, 1, v___x_2541_);
lean_closure_set(v___f_2562_, 2, v___x_2542_);
v___f_2563_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2563_, 0, v_env_2561_);
lean_inc(v_inst_2556_);
lean_inc(v_toBind_2552_);
v___f_2564_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__21___boxed), 22, 21);
lean_closure_set(v___f_2564_, 0, v_inst_2543_);
lean_closure_set(v___f_2564_, 1, v_toMonadRef_2544_);
lean_closure_set(v___f_2564_, 2, v_env_2561_);
lean_closure_set(v___f_2564_, 3, v___x_2545_);
lean_closure_set(v___f_2564_, 4, v___f_2562_);
lean_closure_set(v___f_2564_, 5, v___f_2563_);
lean_closure_set(v___f_2564_, 6, v_toMonadQuotation_2546_);
lean_closure_set(v___f_2564_, 7, v_inst_2547_);
lean_closure_set(v___f_2564_, 8, v_x_2548_);
lean_closure_set(v___f_2564_, 9, v_toPure_2549_);
lean_closure_set(v___f_2564_, 10, v_inst_2550_);
lean_closure_set(v___f_2564_, 11, v___f_2551_);
lean_closure_set(v___f_2564_, 12, v_toBind_2552_);
lean_closure_set(v___f_2564_, 13, v_setNextMacroScope_2553_);
lean_closure_set(v___f_2564_, 14, v_inst_2554_);
lean_closure_set(v___f_2564_, 15, v_inst_2555_);
lean_closure_set(v___f_2564_, 16, v_inst_2556_);
lean_closure_set(v___f_2564_, 17, v_inst_2557_);
lean_closure_set(v___f_2564_, 18, v_inst_2558_);
lean_closure_set(v___f_2564_, 19, v_toMonadExceptOf_2559_);
lean_closure_set(v___f_2564_, 20, v_getNextMacroScope_2560_);
v___x_2565_ = lean_apply_4(v_toBind_2552_, lean_box(0), lean_box(0), v_inst_2556_, v___f_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_2566_ = _args[0];
lean_object* v___x_2567_ = _args[1];
lean_object* v_inst_2568_ = _args[2];
lean_object* v_toMonadRef_2569_ = _args[3];
lean_object* v___x_2570_ = _args[4];
lean_object* v_toMonadQuotation_2571_ = _args[5];
lean_object* v_inst_2572_ = _args[6];
lean_object* v_x_2573_ = _args[7];
lean_object* v_toPure_2574_ = _args[8];
lean_object* v_inst_2575_ = _args[9];
lean_object* v___f_2576_ = _args[10];
lean_object* v_toBind_2577_ = _args[11];
lean_object* v_setNextMacroScope_2578_ = _args[12];
lean_object* v_inst_2579_ = _args[13];
lean_object* v_inst_2580_ = _args[14];
lean_object* v_inst_2581_ = _args[15];
lean_object* v_inst_2582_ = _args[16];
lean_object* v_inst_2583_ = _args[17];
lean_object* v_toMonadExceptOf_2584_ = _args[18];
lean_object* v_getNextMacroScope_2585_ = _args[19];
lean_object* v_env_2586_ = _args[20];
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Elab_liftMacroM___redArg___lam__22(v___x_2566_, v___x_2567_, v_inst_2568_, v_toMonadRef_2569_, v___x_2570_, v_toMonadQuotation_2571_, v_inst_2572_, v_x_2573_, v_toPure_2574_, v_inst_2575_, v___f_2576_, v_toBind_2577_, v_setNextMacroScope_2578_, v_inst_2579_, v_inst_2580_, v_inst_2581_, v_inst_2582_, v_inst_2583_, v_toMonadExceptOf_2584_, v_getNextMacroScope_2585_, v_env_2586_);
return v_res_2587_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__10(void){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_EStateM_nonBacktrackable___redArg();
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__11(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__10, &l_Lean_Elab_liftMacroM___redArg___closed__10_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__10);
v___x_2609_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__12(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___f_2611_; 
v___x_2610_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2611_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2611_, 0, v___x_2610_);
return v___f_2611_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__13(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___f_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__11, &l_Lean_Elab_liftMacroM___redArg___closed__11_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__11);
v___f_2613_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2613_, 0, v___x_2612_);
return v___f_2613_;
}
}
static lean_object* _init_l_Lean_Elab_liftMacroM___redArg___closed__14(void){
_start:
{
lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; 
v___f_2614_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__13, &l_Lean_Elab_liftMacroM___redArg___closed__13_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__13);
v___f_2615_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__12, &l_Lean_Elab_liftMacroM___redArg___closed__12_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__12);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___f_2615_);
lean_ctor_set(v___x_2616_, 1, v___f_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___redArg(lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_x_2628_){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_toApplicative_2631_; lean_object* v_toBind_2632_; lean_object* v_getEnv_2633_; lean_object* v_toMonadExceptOf_2634_; lean_object* v_toMonadRef_2635_; lean_object* v_toMonadQuotation_2636_; lean_object* v_getNextMacroScope_2637_; lean_object* v_setNextMacroScope_2638_; lean_object* v_toPure_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___x_2643_; 
v___x_2629_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__9));
v___x_2630_ = lean_obj_once(&l_Lean_Elab_liftMacroM___redArg___closed__14, &l_Lean_Elab_liftMacroM___redArg___closed__14_once, _init_l_Lean_Elab_liftMacroM___redArg___closed__14);
v_toApplicative_2631_ = lean_ctor_get(v_inst_2619_, 0);
v_toBind_2632_ = lean_ctor_get(v_inst_2619_, 1);
lean_inc_n(v_toBind_2632_, 3);
v_getEnv_2633_ = lean_ctor_get(v_inst_2621_, 0);
lean_inc(v_getEnv_2633_);
v_toMonadExceptOf_2634_ = lean_ctor_get(v_inst_2623_, 0);
lean_inc_ref(v_toMonadExceptOf_2634_);
v_toMonadRef_2635_ = lean_ctor_get(v_inst_2623_, 1);
lean_inc_ref_n(v_toMonadRef_2635_, 2);
v_toMonadQuotation_2636_ = lean_ctor_get(v_inst_2620_, 0);
lean_inc_ref(v_toMonadQuotation_2636_);
v_getNextMacroScope_2637_ = lean_ctor_get(v_inst_2620_, 1);
lean_inc(v_getNextMacroScope_2637_);
v_setNextMacroScope_2638_ = lean_ctor_get(v_inst_2620_, 2);
lean_inc(v_setNextMacroScope_2638_);
lean_dec_ref(v_inst_2620_);
v_toPure_2639_ = lean_ctor_get(v_toApplicative_2631_, 1);
lean_inc_n(v_toPure_2639_, 2);
v___x_2640_ = ((lean_object*)(l_Lean_Elab_liftMacroM___redArg___closed__15));
lean_inc(v_inst_2627_);
lean_inc_ref(v_inst_2619_);
lean_inc(v_inst_2626_);
lean_inc_ref(v_inst_2625_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2641_, 0, v_inst_2625_);
lean_closure_set(v___f_2641_, 1, v_toPure_2639_);
lean_closure_set(v___f_2641_, 2, v_toBind_2632_);
lean_closure_set(v___f_2641_, 3, v_inst_2626_);
lean_closure_set(v___f_2641_, 4, v_inst_2619_);
lean_closure_set(v___f_2641_, 5, v_toMonadRef_2635_);
lean_closure_set(v___f_2641_, 6, v_inst_2627_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___redArg___lam__22___boxed), 21, 20);
lean_closure_set(v___f_2642_, 0, v___x_2630_);
lean_closure_set(v___f_2642_, 1, v___x_2640_);
lean_closure_set(v___f_2642_, 2, v_inst_2624_);
lean_closure_set(v___f_2642_, 3, v_toMonadRef_2635_);
lean_closure_set(v___f_2642_, 4, v___x_2629_);
lean_closure_set(v___f_2642_, 5, v_toMonadQuotation_2636_);
lean_closure_set(v___f_2642_, 6, v_inst_2622_);
lean_closure_set(v___f_2642_, 7, v_x_2628_);
lean_closure_set(v___f_2642_, 8, v_toPure_2639_);
lean_closure_set(v___f_2642_, 9, v_inst_2619_);
lean_closure_set(v___f_2642_, 10, v___f_2641_);
lean_closure_set(v___f_2642_, 11, v_toBind_2632_);
lean_closure_set(v___f_2642_, 12, v_setNextMacroScope_2638_);
lean_closure_set(v___f_2642_, 13, v_inst_2621_);
lean_closure_set(v___f_2642_, 14, v_inst_2625_);
lean_closure_set(v___f_2642_, 15, v_inst_2626_);
lean_closure_set(v___f_2642_, 16, v_inst_2627_);
lean_closure_set(v___f_2642_, 17, v_inst_2623_);
lean_closure_set(v___f_2642_, 18, v_toMonadExceptOf_2634_);
lean_closure_set(v___f_2642_, 19, v_getNextMacroScope_2637_);
v___x_2643_ = lean_apply_4(v_toBind_2632_, lean_box(0), lean_box(0), v_getEnv_2633_, v___f_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM(lean_object* v_m_2644_, lean_object* v_00_u03b1_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2646_, v_inst_2647_, v_inst_2648_, v_inst_2649_, v_inst_2650_, v_inst_2651_, v_inst_2652_, v_inst_2653_, v_inst_2654_, v_x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___boxed(lean_object* v_m_2658_, lean_object* v_00_u03b1_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_x_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Elab_liftMacroM(v_m_2658_, v_00_u03b1_2659_, v_inst_2660_, v_inst_2661_, v_inst_2662_, v_inst_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_inst_2668_, v_inst_2669_, v_x_2670_);
lean_dec(v_inst_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___redArg(lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_x_2681_, lean_object* v_stx_2682_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_apply_1(v_x_2681_, v_stx_2682_);
v___x_2684_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2672_, v_inst_2673_, v_inst_2674_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v___x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro(lean_object* v_m_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_x_2696_, lean_object* v_stx_2697_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_apply_1(v_x_2696_, v_stx_2697_);
v___x_2699_ = l_Lean_Elab_liftMacroM___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_adaptMacro___boxed(lean_object* v_m_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_x_2711_, lean_object* v_stx_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Elab_adaptMacro(v_m_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_x_2711_, v_stx_2712_);
lean_dec(v_inst_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(lean_object* v_baseName_2714_, lean_object* v_currNamespace_2715_, lean_object* v_idx_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_name_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_inc(v_idx_2716_);
lean_inc(v_baseName_2714_);
v_name_2719_ = lean_name_append_index_after(v_baseName_2714_, v_idx_2716_);
lean_inc(v_name_2719_);
lean_inc(v_currNamespace_2715_);
v___x_2720_ = l_Lean_Name_append(v_currNamespace_2715_, v_name_2719_);
v___x_2721_ = l_Lean_Macro_hasDecl(v___x_2720_, v_a_2717_, v_a_2718_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; uint8_t v___x_2723_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
v___x_2723_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
if (v___x_2723_ == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_idx_2716_);
lean_dec(v_currNamespace_2715_);
lean_dec(v_baseName_2714_);
v_a_2724_ = lean_ctor_get(v___x_2721_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v___x_2721_, 0);
lean_dec(v_unused_2732_);
v___x_2726_ = v___x_2721_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2721_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v_name_2719_);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_name_2719_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec(v_name_2719_);
v_a_2733_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2721_, 2);
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_idx_2716_, v___x_2734_);
lean_dec(v_idx_2716_);
v_idx_2716_ = v___x_2735_;
v_a_2718_ = v_a_2733_;
goto _start;
}
}
else
{
lean_object* v_a_2737_; lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_name_2719_);
lean_dec(v_idx_2716_);
lean_dec(v_currNamespace_2715_);
lean_dec(v_baseName_2714_);
v_a_2737_ = lean_ctor_get(v___x_2721_, 0);
v_a_2738_ = lean_ctor_get(v___x_2721_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2721_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_inc(v_a_2737_);
lean_dec(v___x_2721_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2737_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(lean_object* v_baseName_2746_, lean_object* v_currNamespace_2747_, lean_object* v_idx_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2746_, v_currNamespace_2747_, v_idx_2748_, v_a_2749_, v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object* v_baseName_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Macro_getCurrNamespace(v_a_2753_, v_a_2754_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_n(v_a_2756_, 2);
v_a_2757_ = lean_ctor_get(v___x_2755_, 1);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2755_, 2);
lean_inc(v_baseName_2752_);
v___x_2758_ = l_Lean_Name_append(v_a_2756_, v_baseName_2752_);
v___x_2759_ = l_Lean_Macro_hasDecl(v___x_2758_, v_a_2753_, v_a_2757_);
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
lean_dec(v_a_2756_);
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
lean_ctor_set(v___x_2764_, 0, v_baseName_2752_);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_baseName_2752_);
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
v_a_2771_ = lean_ctor_get(v___x_2759_, 1);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2759_, 2);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(v_baseName_2752_, v_a_2756_, v___x_2772_, v_a_2753_, v_a_2771_);
return v___x_2773_;
}
}
else
{
lean_object* v_a_2774_; lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2756_);
lean_dec(v_baseName_2752_);
v_a_2774_ = lean_ctor_get(v___x_2759_, 0);
v_a_2775_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2759_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_inc(v_a_2774_);
lean_dec(v___x_2759_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_dec(v_baseName_2752_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkUnusedBaseName___boxed(lean_object* v_baseName_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_2783_, v_a_2784_, v_a_2785_);
lean_dec_ref(v_a_2784_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Elab_logException___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_Elab_logException___redArg___lam__0___closed__0));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg___lam__0(lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_name_2794_){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = lean_obj_once(&l_Lean_Elab_logException___redArg___lam__0___closed__1, &l_Lean_Elab_logException___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_logException___redArg___lam__0___closed__1);
v___x_2796_ = l_Lean_MessageData_ofName(v_name_2794_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_logError___redArg(v_inst_2790_, v_inst_2791_, v_inst_2792_, v_inst_2793_, v___x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___redArg(lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_ex_2804_){
_start:
{
if (lean_obj_tag(v_ex_2804_) == 0)
{
lean_object* v_ref_2805_; lean_object* v_msg_2806_; lean_object* v___x_2807_; 
lean_dec(v_inst_2803_);
v_ref_2805_ = lean_ctor_get(v_ex_2804_, 0);
lean_inc(v_ref_2805_);
v_msg_2806_ = lean_ctor_get(v_ex_2804_, 1);
lean_inc_ref(v_msg_2806_);
lean_dec_ref_known(v_ex_2804_, 2);
v___x_2807_ = l_Lean_logErrorAt___redArg(v_inst_2799_, v_inst_2800_, v_inst_2801_, v_inst_2802_, v_ref_2805_, v_msg_2806_);
return v___x_2807_;
}
else
{
lean_object* v_toApplicative_2808_; lean_object* v_toBind_2809_; lean_object* v_toPure_2810_; lean_object* v_id_2811_; lean_object* v___f_2812_; uint8_t v___y_2814_; uint8_t v___x_2820_; 
v_toApplicative_2808_ = lean_ctor_get(v_inst_2799_, 0);
v_toBind_2809_ = lean_ctor_get(v_inst_2799_, 1);
lean_inc(v_toBind_2809_);
v_toPure_2810_ = lean_ctor_get(v_toApplicative_2808_, 1);
lean_inc(v_toPure_2810_);
v_id_2811_ = lean_ctor_get(v_ex_2804_, 0);
lean_inc(v_id_2811_);
v___f_2812_ = lean_alloc_closure((void*)(l_Lean_Elab_logException___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2812_, 0, v_inst_2799_);
lean_closure_set(v___f_2812_, 1, v_inst_2800_);
lean_closure_set(v___f_2812_, 2, v_inst_2801_);
lean_closure_set(v___f_2812_, 3, v_inst_2802_);
v___x_2820_ = l_Lean_Elab_isAbortExceptionId(v_id_2811_);
if (v___x_2820_ == 0)
{
uint8_t v___x_2821_; 
v___x_2821_ = l_Lean_Exception_isInterrupt(v_ex_2804_);
lean_dec_ref_known(v_ex_2804_, 2);
v___y_2814_ = v___x_2821_;
goto v___jp_2813_;
}
else
{
lean_dec_ref_known(v_ex_2804_, 2);
v___y_2814_ = v___x_2820_;
goto v___jp_2813_;
}
v___jp_2813_:
{
if (v___y_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec(v_toPure_2810_);
v___x_2815_ = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(v___x_2815_, 0, v_id_2811_);
v___x_2816_ = lean_apply_2(v_inst_2803_, lean_box(0), v___x_2815_);
v___x_2817_ = lean_apply_4(v_toBind_2809_, lean_box(0), lean_box(0), v___x_2816_, v___f_2812_);
return v___x_2817_;
}
else
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v___f_2812_);
lean_dec(v_id_2811_);
lean_dec(v_toBind_2809_);
lean_dec(v_inst_2803_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_apply_2(v_toPure_2810_, lean_box(0), v___x_2818_);
return v___x_2819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException(lean_object* v_m_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_ex_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Elab_logException___redArg(v_inst_2823_, v_inst_2824_, v_inst_2825_, v_inst_2826_, v_inst_2827_, v_ex_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg___lam__0(lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_ex_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Elab_logException___redArg(v_inst_2830_, v_inst_2831_, v_inst_2832_, v_inst_2833_, v_inst_2834_, v_ex_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___redArg(lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_inst_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v_tryCatch_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; 
v_tryCatch_2844_ = lean_ctor_get(v_inst_2839_, 1);
lean_inc(v_tryCatch_2844_);
lean_dec_ref(v_inst_2839_);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Elab_withLogging___redArg___lam__0), 6, 5);
lean_closure_set(v___f_2845_, 0, v_inst_2837_);
lean_closure_set(v___f_2845_, 1, v_inst_2838_);
lean_closure_set(v___f_2845_, 2, v_inst_2840_);
lean_closure_set(v___f_2845_, 3, v_inst_2841_);
lean_closure_set(v___f_2845_, 4, v_inst_2842_);
v___x_2846_ = lean_apply_3(v_tryCatch_2844_, lean_box(0), v_x_2843_, v___f_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging(lean_object* v_m_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_, lean_object* v_x_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Elab_withLogging___redArg(v_inst_2848_, v_inst_2849_, v_inst_2850_, v_inst_2851_, v_inst_2852_, v_inst_2853_, v_x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = ((lean_object*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0));
v___x_2858_ = l_Lean_stringToMessageData(v___x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(lean_object* v_val_2859_, lean_object* v_ex_2860_, lean_object* v_toPure_2861_, lean_object* v_____do__lift_2862_){
_start:
{
lean_object* v_exPosition_2863_; lean_object* v_line_2864_; lean_object* v_column_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2885_; 
v_exPosition_2863_ = l_Lean_FileMap_toPosition(v_____do__lift_2862_, v_val_2859_);
v_line_2864_ = lean_ctor_get(v_exPosition_2863_, 0);
v_column_2865_ = lean_ctor_get(v_exPosition_2863_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_exPosition_2863_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2867_ = v_exPosition_2863_;
v_isShared_2868_ = v_isSharedCheck_2885_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_column_2865_);
lean_inc(v_line_2864_);
lean_dec(v_exPosition_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2885_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2869_ = l_Nat_reprFast(v_line_2864_);
v___x_2870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___x_2871_ = l_Lean_MessageData_ofFormat(v___x_2870_);
v___x_2872_ = lean_obj_once(&l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1, &l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1);
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 7);
lean_ctor_set(v___x_2867_, 1, v___x_2872_);
lean_ctor_set(v___x_2867_, 0, v___x_2871_);
v___x_2874_ = v___x_2867_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2875_ = l_Nat_reprFast(v_column_2865_);
v___x_2876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
v___x_2877_ = l_Lean_MessageData_ofFormat(v___x_2876_);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2874_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16);
v___x_2880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = l_Lean_Exception_toMessageData(v_ex_2860_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_apply_2(v_toPure_2861_, lean_box(0), v___x_2882_);
return v___x_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(lean_object* v_val_2886_, lean_object* v_ex_2887_, lean_object* v_toPure_2888_, lean_object* v_____do__lift_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(v_val_2886_, v_ex_2887_, v_toPure_2888_, v_____do__lift_2889_);
lean_dec(v_val_2886_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(lean_object* v_ex_2891_, lean_object* v_toPure_2892_, lean_object* v_toBind_2893_, lean_object* v_toMonadFileMap_2894_, lean_object* v_pos_2895_){
_start:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = l_Lean_Exception_getRef(v_ex_2891_);
v___x_2897_ = 0;
v___x_2898_ = l_Lean_Syntax_getPos_x3f(v___x_2896_, v___x_2897_);
lean_dec(v___x_2896_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v_toMonadFileMap_2894_);
lean_dec(v_toBind_2893_);
v___x_2899_ = l_Lean_Exception_toMessageData(v_ex_2891_);
v___x_2900_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2899_);
return v___x_2900_;
}
else
{
lean_object* v_val_2901_; uint8_t v_decide_2902_; 
v_val_2901_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_val_2901_);
lean_dec_ref_known(v___x_2898_, 1);
v_decide_2902_ = lean_nat_dec_eq(v_pos_2895_, v_val_2901_);
if (v_decide_2902_ == 0)
{
lean_object* v___f_2903_; lean_object* v___x_2904_; 
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2903_, 0, v_val_2901_);
lean_closure_set(v___f_2903_, 1, v_ex_2891_);
lean_closure_set(v___f_2903_, 2, v_toPure_2892_);
v___x_2904_ = lean_apply_4(v_toBind_2893_, lean_box(0), lean_box(0), v_toMonadFileMap_2894_, v___f_2903_);
return v___x_2904_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v_val_2901_);
lean_dec(v_toMonadFileMap_2894_);
lean_dec(v_toBind_2893_);
v___x_2905_ = l_Lean_Exception_toMessageData(v_ex_2891_);
v___x_2906_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2905_);
return v___x_2906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(lean_object* v_ex_2907_, lean_object* v_toPure_2908_, lean_object* v_toBind_2909_, lean_object* v_toMonadFileMap_2910_, lean_object* v_pos_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(v_ex_2907_, v_toPure_2908_, v_toBind_2909_, v_toMonadFileMap_2910_, v_pos_2911_);
lean_dec(v_pos_2911_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___redArg(lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_ex_2915_){
_start:
{
lean_object* v_toApplicative_2916_; lean_object* v_toBind_2917_; lean_object* v_toPure_2918_; lean_object* v_toMonadFileMap_2919_; lean_object* v___x_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; 
v_toApplicative_2916_ = lean_ctor_get(v_inst_2913_, 0);
v_toBind_2917_ = lean_ctor_get(v_inst_2913_, 1);
lean_inc_n(v_toBind_2917_, 2);
v_toPure_2918_ = lean_ctor_get(v_toApplicative_2916_, 1);
lean_inc(v_toPure_2918_);
v_toMonadFileMap_2919_ = lean_ctor_get(v_inst_2914_, 0);
lean_inc(v_toMonadFileMap_2919_);
v___x_2920_ = l_Lean_getRefPos___redArg(v_inst_2913_, v_inst_2914_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2921_, 0, v_ex_2915_);
lean_closure_set(v___f_2921_, 1, v_toPure_2918_);
lean_closure_set(v___f_2921_, 2, v_toBind_2917_);
lean_closure_set(v___f_2921_, 3, v_toMonadFileMap_2919_);
v___x_2922_ = lean_apply_4(v_toBind_2917_, lean_box(0), lean_box(0), v___x_2920_, v___f_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData(lean_object* v_m_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_ex_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2924_, v_inst_2925_, v_ex_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_2928_, v_inst_2929_, v_x_2930_);
return v___x_2931_;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(lean_object* v_msg_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_____do__lift_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2939_ = lean_obj_once(&l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1, &l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1);
v___x_2940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_msg_2935_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = l_Lean_toMessageList(v_____do__lift_2938_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l_Lean_throwError___redArg(v_inst_2936_, v_inst_2937_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_msg_2947_, lean_object* v_exs_2948_){
_start:
{
lean_object* v_toBind_2949_; lean_object* v___f_2950_; lean_object* v___f_2951_; size_t v_sz_2952_; size_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_toBind_2949_ = lean_ctor_get(v_inst_2945_, 1);
lean_inc(v_toBind_2949_);
lean_inc_ref_n(v_inst_2945_, 2);
v___f_2950_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2950_, 0, v_inst_2945_);
lean_closure_set(v___f_2950_, 1, v_inst_2946_);
v___f_2951_ = lean_alloc_closure((void*)(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2951_, 0, v_msg_2947_);
lean_closure_set(v___f_2951_, 1, v_inst_2945_);
lean_closure_set(v___f_2951_, 2, v_inst_2944_);
v_sz_2952_ = lean_array_size(v_exs_2948_);
v___x_2953_ = ((size_t)0ULL);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2945_, v___f_2950_, v_sz_2952_, v___x_2953_, v_exs_2948_);
v___x_2955_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2954_, v___f_2951_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors(lean_object* v_m_2956_, lean_object* v_00_u03b1_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_msg_2961_, lean_object* v_exs_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v_inst_2958_, v_inst_2959_, v_inst_2960_, v_msg_2961_, v_exs_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3030_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3031_ = 0;
v___x_3032_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3033_ = l_Lean_registerTraceClass(v___x_3030_, v___x_3031_, v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref_known(v___x_3033_, 1);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3035_ = l_Lean_registerTraceClass(v___x_3034_, v___x_3031_, v___x_3032_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = ((lean_object*)(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_));
v___x_3037_ = 1;
v___x_3038_ = l_Lean_registerTraceClass(v___x_3036_, v___x_3037_, v___x_3032_);
return v___x_3038_;
}
else
{
return v___x_3035_;
}
}
else
{
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
return v_res_3040_;
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
