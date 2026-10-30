// Lean compiler output
// Module: Lean.Parser.Tactic.Doc
// Imports: public import Lean.Environment import Lean.Elab.InfoTree.Main meta import Lean.Parser.Attr import Lean.Parser.Extension import Lean.ExtraModUses
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Parser_getSyntaxNodeKindCategories(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_isTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_Doc_isTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_isTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Doc_isTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Doc_isTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic_Doc_isTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_isTactic___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_isTactic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticAlternativeExt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 146, 24, 182, 49, 189, 94, 210)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 93, 47, 100, 105, 134, 228, 150)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "` is itself an alternative for `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` is not a tactic (it is in the categor"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ies"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Invalid `["};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` attribute syntax"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 29, 168, 181, 197, 113, 106, 176)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 168, 115, 176, 65, 44, 32, 74)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 127, 150, 230, 147, 51, 9, 44)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(171, 201, 216, 96, 187, 41, 25, 8)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(150, 217, 225, 249, 92, 227, 115, 9)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 73, 235, 188, 43, 204, 182, 169)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 40, 120, 84, 223, 15, 213, 179)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 14, 153, 180, 178, 10, 178, 110)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 228, 109, 71, 114, 58, 146, 87)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 220, 235, 94, 119, 251, 240, 121)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 121, 233, 68, 41, 52, 222, 209)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 103, 238, 221, 135, 73, 246, 74)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 42, 205, 170, 76, 149, 101, 166)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 231, 66, 168, 91, 162, 207, 65)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 120, .m_data = "Register a tactic parser as an alternative form of an existing tactic, so they can be grouped together in documentation."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "knownTacticTagExt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 146, 24, 182, 49, 189, 94, 210)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 95, 108, 201, 158, 34, 35, 73)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
static const lean_ctor_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticTagExt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 146, 24, 182, 49, 189, 94, 210)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 16, 159, 45, 73, 112, 111, 154)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(expected "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Unknown tag `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "one of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", ..."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__12_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "(no tags defined)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_tag"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 132, 153, 94, 172, 4, 109, 157)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1176478476) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(6, 145, 207, 84, 40, 68, 96, 133)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 222, 3, 19, 240, 88, 68, 38)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 217, 170, 202, 224, 178, 78, 10)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(228, 145, 95, 106, 189, 62, 63, 24)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "Register a tactic parser as an alternative of an existing tactic, so they can be grouped together in documentation."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tacticDocExtExt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 146, 24, 182, 49, 189, 94, 210)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 237, 208, 207, 38, 173, 216, 107)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "   "};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " * "};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n\nExtensions:\n\n"};
static const lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticNameExt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 146, 24, 182, 49, 189, 94, 210)}};
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 229, 37, 106, 74, 105, 187, 225)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "The tactic `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` already has the custom name `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "` is defined in an imported module, but custom names can only be added in the tactic's defining module."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is defined in `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "`, but custom names can only be added in the tactic's defining module."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_name"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 250, 159, 49, 179, 121, 155, 115)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "Registers a custom name for a tactic. This custom name should be a prefix of the tactic's syntax, because it is used in completion."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "` is not a tactic, but it was assigned a tactic name `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0 = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(lean_object* v_keys_1_, lean_object* v_i_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_array_get_size(v_keys_1_);
v___x_5_ = lean_nat_dec_lt(v_i_2_, v___x_4_);
if (v___x_5_ == 0)
{
lean_dec(v_i_2_);
return v___x_5_;
}
else
{
lean_object* v_k_x27_6_; uint8_t v___x_7_; 
v_k_x27_6_ = lean_array_fget_borrowed(v_keys_1_, v_i_2_);
v___x_7_ = lean_name_eq(v_k_3_, v_k_x27_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_i_2_, v___x_8_);
lean_dec(v_i_2_);
v_i_2_ = v___x_9_;
goto _start;
}
else
{
lean_dec(v_i_2_);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_keys_11_, lean_object* v_i_12_, lean_object* v_k_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_keys_11_, v_i_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec_ref(v_keys_11_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(lean_object* v_x_16_, size_t v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v_es_19_; lean_object* v___x_20_; size_t v___x_21_; size_t v___x_22_; lean_object* v_j_23_; lean_object* v___x_24_; 
v_es_19_ = lean_ctor_get(v_x_16_, 0);
v___x_20_ = lean_box(2);
v___x_21_ = ((size_t)31ULL);
v___x_22_ = lean_usize_land(v_x_17_, v___x_21_);
v_j_23_ = lean_usize_to_nat(v___x_22_);
v___x_24_ = lean_array_get_borrowed(v___x_20_, v_es_19_, v_j_23_);
lean_dec(v_j_23_);
switch(lean_obj_tag(v___x_24_))
{
case 0:
{
lean_object* v_key_25_; uint8_t v___x_26_; 
v_key_25_ = lean_ctor_get(v___x_24_, 0);
v___x_26_ = lean_name_eq(v_x_18_, v_key_25_);
return v___x_26_;
}
case 1:
{
lean_object* v_node_27_; size_t v___x_28_; size_t v___x_29_; 
v_node_27_ = lean_ctor_get(v___x_24_, 0);
v___x_28_ = ((size_t)5ULL);
v___x_29_ = lean_usize_shift_right(v_x_17_, v___x_28_);
v_x_16_ = v_node_27_;
v_x_17_ = v___x_29_;
goto _start;
}
default: 
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
}
else
{
lean_object* v_ks_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_ks_32_ = lean_ctor_get(v_x_16_, 0);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_ks_32_, v___x_33_, v_x_18_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___boxed(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
size_t v_x_357__boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_x_357__boxed_38_ = lean_unbox_usize(v_x_36_);
lean_dec(v_x_36_);
v_res_39_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_35_, v_x_357__boxed_38_, v_x_37_);
lean_dec(v_x_37_);
lean_dec_ref(v_x_35_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint64_t v___y_44_; 
if (lean_obj_tag(v_x_42_) == 0)
{
uint64_t v___x_47_; 
v___x_47_ = 1723ULL;
v___y_44_ = v___x_47_;
goto v___jp_43_;
}
else
{
uint64_t v_hash_48_; 
v_hash_48_ = lean_ctor_get_uint64(v_x_42_, sizeof(void*)*2);
v___y_44_ = v_hash_48_;
goto v___jp_43_;
}
v___jp_43_:
{
size_t v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_uint64_to_usize(v___y_44_);
v___x_46_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_41_, v___x_45_, v_x_42_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_49_, v_x_50_);
lean_dec(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_53_, lean_object* v_vals_54_, lean_object* v_i_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_get_size(v_keys_53_);
v___x_58_ = lean_nat_dec_lt(v_i_55_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
lean_dec(v_i_55_);
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
lean_object* v_k_x27_60_; uint8_t v___x_61_; 
v_k_x27_60_ = lean_array_fget_borrowed(v_keys_53_, v_i_55_);
v___x_61_ = lean_name_eq(v_k_56_, v_k_x27_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_i_55_, v___x_62_);
lean_dec(v_i_55_);
v_i_55_ = v___x_63_;
goto _start;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_array_fget_borrowed(v_vals_54_, v_i_55_);
lean_dec(v_i_55_);
lean_inc(v___x_65_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_67_, lean_object* v_vals_68_, lean_object* v_i_69_, lean_object* v_k_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_67_, v_vals_68_, v_i_69_, v_k_70_);
lean_dec(v_k_70_);
lean_dec_ref(v_vals_68_);
lean_dec_ref(v_keys_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(lean_object* v_x_72_, size_t v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_es_75_; lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_j_79_; lean_object* v___x_80_; 
v_es_75_ = lean_ctor_get(v_x_72_, 0);
v___x_76_ = lean_box(2);
v___x_77_ = ((size_t)31ULL);
v___x_78_ = lean_usize_land(v_x_73_, v___x_77_);
v_j_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_array_get_borrowed(v___x_76_, v_es_75_, v_j_79_);
lean_dec(v_j_79_);
switch(lean_obj_tag(v___x_80_))
{
case 0:
{
lean_object* v_key_81_; lean_object* v_val_82_; uint8_t v___x_83_; 
v_key_81_ = lean_ctor_get(v___x_80_, 0);
v_val_82_ = lean_ctor_get(v___x_80_, 1);
v___x_83_ = lean_name_eq(v_x_74_, v_key_81_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
lean_inc(v_val_82_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_val_82_);
return v___x_85_;
}
}
case 1:
{
lean_object* v_node_86_; size_t v___x_87_; size_t v___x_88_; 
v_node_86_ = lean_ctor_get(v___x_80_, 0);
v___x_87_ = ((size_t)5ULL);
v___x_88_ = lean_usize_shift_right(v_x_73_, v___x_87_);
v_x_72_ = v_node_86_;
v_x_73_ = v___x_88_;
goto _start;
}
default: 
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
}
else
{
lean_object* v_ks_91_; lean_object* v_vs_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_ks_91_ = lean_ctor_get(v_x_72_, 0);
v_vs_92_ = lean_ctor_get(v_x_72_, 1);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_ks_91_, v_vs_92_, v___x_93_, v_x_74_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg___boxed(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
size_t v_x_432__boxed_98_; lean_object* v_res_99_; 
v_x_432__boxed_98_ = lean_unbox_usize(v_x_96_);
lean_dec(v_x_96_);
v_res_99_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_95_, v_x_432__boxed_98_, v_x_97_);
lean_dec(v_x_97_);
lean_dec_ref(v_x_95_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint64_t v___y_103_; 
if (lean_obj_tag(v_x_101_) == 0)
{
uint64_t v___x_106_; 
v___x_106_ = 1723ULL;
v___y_103_ = v___x_106_;
goto v___jp_102_;
}
else
{
uint64_t v_hash_107_; 
v_hash_107_ = lean_ctor_get_uint64(v_x_101_, sizeof(void*)*2);
v___y_103_ = v_hash_107_;
goto v___jp_102_;
}
v___jp_102_:
{
size_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_uint64_to_usize(v___y_103_);
v___x_105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_100_, v___x_104_, v_x_101_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_108_, v_x_109_);
lean_dec(v_x_109_);
lean_dec_ref(v_x_108_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object* v_env_114_, lean_object* v_kind_115_){
_start:
{
lean_object* v___x_116_; lean_object* v_ext_117_; lean_object* v_toEnvExtension_118_; lean_object* v_asyncMode_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v_categories_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_116_ = l_Lean_Parser_parserExtension;
v_ext_117_ = lean_ctor_get(v___x_116_, 1);
v_toEnvExtension_118_ = lean_ctor_get(v_ext_117_, 0);
v_asyncMode_119_ = lean_ctor_get(v_toEnvExtension_118_, 2);
v___x_120_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_121_ = 0;
v___x_122_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_120_, v___x_116_, v_env_114_, v_asyncMode_119_, v___x_121_);
v_categories_123_ = lean_ctor_get(v___x_122_, 2);
lean_inc_ref(v_categories_123_);
lean_dec(v___x_122_);
v___x_124_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_125_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_categories_123_, v___x_124_);
lean_dec_ref(v_categories_123_);
if (lean_obj_tag(v___x_125_) == 1)
{
lean_object* v_val_126_; lean_object* v_kinds_127_; uint8_t v___x_128_; 
v_val_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v___x_125_, 1);
v_kinds_127_ = lean_ctor_get(v_val_126_, 1);
lean_inc_ref(v_kinds_127_);
lean_dec(v_val_126_);
v___x_128_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_127_, v_kind_115_);
lean_dec_ref(v_kinds_127_);
return v___x_128_;
}
else
{
lean_dec(v___x_125_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_isTactic___boxed(lean_object* v_env_129_, lean_object* v_kind_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_129_, v_kind_130_);
lean_dec(v_kind_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(lean_object* v_00_u03b2_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_134_, v_x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___boxed(lean_object* v_00_u03b2_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(v_00_u03b2_137_, v_x_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec_ref(v_x_138_);
return v_res_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(lean_object* v_00_u03b2_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___boxed(lean_object* v_00_u03b2_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(v_00_u03b2_145_, v_x_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec_ref(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(lean_object* v_00_u03b2_150_, lean_object* v_x_151_, size_t v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_151_, v_x_152_, v_x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___boxed(lean_object* v_00_u03b2_155_, lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
size_t v_x_536__boxed_159_; lean_object* v_res_160_; 
v_x_536__boxed_159_ = lean_unbox_usize(v_x_157_);
lean_dec(v_x_157_);
v_res_160_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(v_00_u03b2_155_, v_x_156_, v_x_536__boxed_159_, v_x_158_);
lean_dec(v_x_158_);
lean_dec_ref(v_x_156_);
return v_res_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(lean_object* v_00_u03b2_161_, lean_object* v_x_162_, size_t v_x_163_, lean_object* v_x_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_162_, v_x_163_, v_x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___boxed(lean_object* v_00_u03b2_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
size_t v_x_547__boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_x_547__boxed_170_ = lean_unbox_usize(v_x_168_);
lean_dec(v_x_168_);
v_res_171_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(v_00_u03b2_166_, v_x_167_, v_x_547__boxed_170_, v_x_169_);
lean_dec(v_x_169_);
lean_dec_ref(v_x_167_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_173_, lean_object* v_keys_174_, lean_object* v_vals_175_, lean_object* v_heq_176_, lean_object* v_i_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_174_, v_vals_175_, v_i_177_, v_k_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_180_, lean_object* v_keys_181_, lean_object* v_vals_182_, lean_object* v_heq_183_, lean_object* v_i_184_, lean_object* v_k_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(v_00_u03b2_180_, v_keys_181_, v_vals_182_, v_heq_183_, v_i_184_, v_k_185_);
lean_dec(v_k_185_);
lean_dec_ref(v_vals_182_);
lean_dec_ref(v_keys_181_);
return v_res_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_187_, lean_object* v_keys_188_, lean_object* v_vals_189_, lean_object* v_heq_190_, lean_object* v_i_191_, lean_object* v_k_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_keys_188_, v_i_191_, v_k_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_194_, lean_object* v_keys_195_, lean_object* v_vals_196_, lean_object* v_heq_197_, lean_object* v_i_198_, lean_object* v_k_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(v_00_u03b2_194_, v_keys_195_, v_vals_196_, v_heq_197_, v_i_198_, v_k_199_);
lean_dec(v_k_199_);
lean_dec_ref(v_vals_196_);
lean_dec_ref(v_keys_195_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_as_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_fst_204_; lean_object* v_snd_205_; lean_object* v___x_206_; 
v_fst_204_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_fst_204_);
v_snd_205_ = lean_ctor_get(v_x_203_, 1);
lean_inc(v_snd_205_);
lean_dec_ref(v_x_203_);
v___x_206_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_204_, v_snd_205_, v_as_202_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_207_, lean_object* v_pivot_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_k_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_lt(v_k_211_, v_hi_207_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_k_211_);
v___x_213_ = lean_array_fswap(v_as_209_, v_i_210_, v_hi_207_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_i_210_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v_fst_216_; lean_object* v_fst_217_; uint8_t v___x_218_; 
v___x_215_ = lean_array_fget_borrowed(v_as_209_, v_k_211_);
v_fst_216_ = lean_ctor_get(v___x_215_, 0);
v_fst_217_ = lean_ctor_get(v_pivot_208_, 0);
v___x_218_ = l_Lean_Name_quickLt(v_fst_216_, v_fst_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_k_211_, v___x_219_);
lean_dec(v_k_211_);
v_k_211_ = v___x_220_;
goto _start;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_array_fswap(v_as_209_, v_i_210_, v_k_211_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_i_210_, v___x_223_);
lean_dec(v_i_210_);
v___x_225_ = lean_nat_add(v_k_211_, v___x_223_);
lean_dec(v_k_211_);
v_as_209_ = v___x_222_;
v_i_210_ = v___x_224_;
v_k_211_ = v___x_225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_227_, lean_object* v_pivot_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_227_, v_pivot_228_, v_as_229_, v_i_230_, v_k_231_);
lean_dec_ref(v_pivot_228_);
lean_dec(v_hi_227_);
return v_res_232_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_233_, lean_object* v_x2_234_){
_start:
{
lean_object* v_fst_235_; lean_object* v_fst_236_; uint8_t v___x_237_; 
v_fst_235_ = lean_ctor_get(v_x1_233_, 0);
v_fst_236_ = lean_ctor_get(v_x2_234_, 0);
v___x_237_ = l_Lean_Name_quickLt(v_fst_235_, v_fst_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_238_, lean_object* v_x2_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_238_, v_x2_239_);
lean_dec_ref(v_x2_239_);
lean_dec_ref(v_x1_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_242_, lean_object* v_as_243_, lean_object* v_lo_244_, lean_object* v_hi_245_){
_start:
{
lean_object* v___y_247_; uint8_t v___x_257_; 
v___x_257_ = lean_nat_dec_lt(v_lo_244_, v_hi_245_);
if (v___x_257_ == 0)
{
lean_dec(v_lo_244_);
return v_as_243_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_mid_260_; lean_object* v___y_262_; lean_object* v___y_268_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_258_ = lean_nat_add(v_lo_244_, v_hi_245_);
v___x_259_ = lean_unsigned_to_nat(1u);
v_mid_260_ = lean_nat_shiftr(v___x_258_, v___x_259_);
lean_dec(v___x_258_);
v___x_273_ = lean_array_fget_borrowed(v_as_243_, v_mid_260_);
v___x_274_ = lean_array_fget_borrowed(v_as_243_, v_lo_244_);
v___x_275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_268_ = v_as_243_;
goto v___jp_267_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_array_fswap(v_as_243_, v_lo_244_, v_mid_260_);
v___y_268_ = v___x_276_;
goto v___jp_267_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_array_fget_borrowed(v___y_262_, v_mid_260_);
v___x_264_ = lean_array_fget_borrowed(v___y_262_, v_hi_245_);
v___x_265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_mid_260_);
v___y_247_ = v___y_262_;
goto v___jp_246_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_array_fswap(v___y_262_, v_mid_260_, v_hi_245_);
lean_dec(v_mid_260_);
v___y_247_ = v___x_266_;
goto v___jp_246_;
}
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_array_fget_borrowed(v___y_268_, v_hi_245_);
v___x_270_ = lean_array_fget_borrowed(v___y_268_, v_lo_244_);
v___x_271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
v___y_262_ = v___y_268_;
goto v___jp_261_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_array_fswap(v___y_268_, v_lo_244_, v_hi_245_);
v___y_262_ = v___x_272_;
goto v___jp_261_;
}
}
}
v___jp_246_:
{
lean_object* v_pivot_248_; lean_object* v___x_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; uint8_t v___x_252_; 
v_pivot_248_ = lean_array_fget(v___y_247_, v_hi_245_);
lean_inc_n(v_lo_244_, 2);
v___x_249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_245_, v_pivot_248_, v___y_247_, v_lo_244_, v_lo_244_);
lean_dec(v_pivot_248_);
v_fst_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v___x_249_);
v___x_252_ = lean_nat_dec_le(v_hi_245_, v_fst_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_242_, v_snd_251_, v_lo_244_, v_fst_250_);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_fst_250_, v___x_254_);
lean_dec(v_fst_250_);
v_as_243_ = v___x_253_;
v_lo_244_ = v___x_255_;
goto _start;
}
else
{
lean_dec(v_fst_250_);
lean_dec(v_lo_244_);
return v_snd_251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_277_, lean_object* v_as_278_, lean_object* v_lo_279_, lean_object* v_hi_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_277_, v_as_278_, v_lo_279_, v_hi_280_);
lean_dec(v_hi_280_);
lean_dec(v_n_277_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_k_284_; lean_object* v_v_285_; lean_object* v_l_286_; lean_object* v_r_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_k_284_ = lean_ctor_get(v_x_283_, 1);
v_v_285_ = lean_ctor_get(v_x_283_, 2);
v_l_286_ = lean_ctor_get(v_x_283_, 3);
v_r_287_ = lean_ctor_get(v_x_283_, 4);
v___x_288_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_282_, v_l_286_);
lean_inc(v_v_285_);
lean_inc(v_k_284_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_k_284_);
lean_ctor_set(v___x_289_, 1, v_v_285_);
v___x_290_ = lean_array_push(v___x_288_, v___x_289_);
v_init_282_ = v___x_290_;
v_x_283_ = v_r_287_;
goto _start;
}
else
{
return v_init_282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_292_, v_x_293_);
lean_dec(v_x_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_297_, lean_object* v_s_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___x_308_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_301_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_300_, v_s_298_);
v___x_302_ = lean_array_get_size(v___x_301_);
v___x_308_ = lean_nat_dec_eq(v___x_302_, v___x_299_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___y_312_; uint8_t v___x_314_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_sub(v___x_302_, v___x_309_);
v___x_314_ = lean_nat_dec_le(v___x_299_, v___x_310_);
if (v___x_314_ == 0)
{
lean_inc(v___x_310_);
v___y_312_ = v___x_310_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___x_299_;
goto v___jp_311_;
}
v___jp_311_:
{
uint8_t v___x_313_; 
v___x_313_ = lean_nat_dec_le(v___y_312_, v___x_310_);
if (v___x_313_ == 0)
{
lean_dec(v___x_310_);
lean_inc(v___y_312_);
v___y_304_ = v___y_312_;
v___y_305_ = v___y_312_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___y_312_;
v___y_305_ = v___x_310_;
goto v___jp_303_;
}
}
}
else
{
lean_object* v___x_315_; 
lean_inc_ref_n(v___x_301_, 2);
v___x_315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_301_);
lean_ctor_set(v___x_315_, 1, v___x_301_);
lean_ctor_set(v___x_315_, 2, v___x_301_);
return v___x_315_;
}
v___jp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_302_, v___x_301_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_inc_ref_n(v___x_306_, 2);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_ctor_set(v___x_307_, 2, v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_316_, lean_object* v_s_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_316_, v_s_317_);
lean_dec(v_s_317_);
lean_dec_ref(v_x_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_321_);
lean_dec(v_x_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_es_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_326_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_325_, v_es_323_);
v___x_327_ = lean_array_get_size(v___x_326_);
v___x_328_ = lean_nat_dec_eq(v___x_327_, v___x_324_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___y_332_; uint8_t v___x_336_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_sub(v___x_327_, v___x_329_);
v___x_336_ = lean_nat_dec_le(v___x_324_, v___x_330_);
if (v___x_336_ == 0)
{
lean_inc(v___x_330_);
v___y_332_ = v___x_330_;
goto v___jp_331_;
}
else
{
v___y_332_ = v___x_324_;
goto v___jp_331_;
}
v___jp_331_:
{
uint8_t v___x_333_; 
v___x_333_ = lean_nat_dec_le(v___y_332_, v___x_330_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v___x_330_);
lean_inc(v___y_332_);
v___x_334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_327_, v___x_326_, v___y_332_, v___y_332_);
lean_dec(v___y_332_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_327_, v___x_326_, v___y_332_, v___x_330_);
lean_dec(v___x_330_);
return v___x_335_;
}
}
}
else
{
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_es_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_es_337_);
lean_dec(v_es_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_345_, lean_object* v_x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_345_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_350_, lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_350_, v_x_351_, v___y_352_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_x_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_389_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object* v_init_392_, lean_object* v_t_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_392_, v_t_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_395_, lean_object* v_t_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(v_init_395_, v_t_396_);
lean_dec(v_t_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object* v_n_398_, lean_object* v_as_399_, lean_object* v_lo_400_, lean_object* v_hi_401_, lean_object* v_w_402_, lean_object* v_hlo_403_, lean_object* v_hhi_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_398_, v_as_399_, v_lo_400_, v_hi_401_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_406_, lean_object* v_as_407_, lean_object* v_lo_408_, lean_object* v_hi_409_, lean_object* v_w_410_, lean_object* v_hlo_411_, lean_object* v_hhi_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(v_n_406_, v_as_407_, v_lo_408_, v_hi_409_, v_w_410_, v_hlo_411_, v_hhi_412_);
lean_dec(v_hi_409_);
lean_dec(v_n_406_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_414_, lean_object* v_lo_415_, lean_object* v_hi_416_, lean_object* v_hhi_417_, lean_object* v_pivot_418_, lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_k_421_, lean_object* v_ilo_422_, lean_object* v_ik_423_, lean_object* v_w_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_416_, v_pivot_418_, v_as_419_, v_i_420_, v_k_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_426_, lean_object* v_lo_427_, lean_object* v_hi_428_, lean_object* v_hhi_429_, lean_object* v_pivot_430_, lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_k_433_, lean_object* v_ilo_434_, lean_object* v_ik_435_, lean_object* v_w_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(v_n_426_, v_lo_427_, v_hi_428_, v_hhi_429_, v_pivot_430_, v_as_431_, v_i_432_, v_k_433_, v_ilo_434_, v_ik_435_, v_w_436_);
lean_dec_ref(v_pivot_430_);
lean_dec(v_hi_428_);
lean_dec(v_lo_427_);
lean_dec(v_n_426_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object* v_as_438_, lean_object* v_k_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_m_444_; lean_object* v_a_445_; uint8_t v___x_446_; 
v___x_442_ = lean_nat_add(v_x_440_, v_x_441_);
v___x_443_ = lean_unsigned_to_nat(1u);
v_m_444_ = lean_nat_shiftr(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
v_a_445_ = lean_array_fget_borrowed(v_as_438_, v_m_444_);
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_445_, v_k_439_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
lean_dec(v_x_441_);
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_439_, v_a_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec(v_m_444_);
lean_dec(v_x_440_);
lean_inc(v_a_445_);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_445_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v_m_444_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_nat_sub(v_m_444_, v___x_443_);
lean_dec(v_m_444_);
v___x_452_ = lean_nat_dec_lt(v___x_451_, v_x_440_);
if (v___x_452_ == 0)
{
v_x_441_ = v___x_451_;
goto _start;
}
else
{
lean_object* v___x_454_; 
lean_dec(v___x_451_);
lean_dec(v_x_440_);
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
else
{
lean_object* v___x_455_; 
lean_dec(v_m_444_);
lean_dec(v_x_440_);
v___x_455_ = lean_box(0);
return v___x_455_;
}
}
}
else
{
lean_object* v___x_456_; uint8_t v___x_457_; 
lean_dec(v_x_440_);
v___x_456_ = lean_nat_add(v_m_444_, v___x_443_);
lean_dec(v_m_444_);
v___x_457_ = lean_nat_dec_le(v___x_456_, v_x_441_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v___x_456_);
lean_dec(v_x_441_);
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
v_x_440_ = v___x_456_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object* v_as_460_, lean_object* v_k_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_460_, v_k_461_, v_x_462_, v_x_463_);
lean_dec_ref(v_k_461_);
lean_dec_ref(v_as_460_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object* v_env_465_, lean_object* v_tac_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_box(1);
v___x_468_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_465_, v_tac_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; lean_object* v_toEnvExtension_470_; lean_object* v_asyncMode_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_469_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_470_ = lean_ctor_get(v___x_469_, 0);
v_asyncMode_471_ = lean_ctor_get(v_toEnvExtension_470_, 2);
v___x_472_ = lean_box(0);
v___x_473_ = 0;
v___x_474_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_467_, v___x_469_, v_env_465_, v_asyncMode_471_, v___x_472_, v___x_473_);
v___x_475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_474_, v_tac_466_);
lean_dec(v_tac_466_);
lean_dec(v___x_474_);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_val_476_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_468_, 1);
v___x_477_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v___x_478_ = 0;
v___x_479_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_467_, v___x_477_, v_env_465_, v_val_476_, v___x_478_);
lean_dec(v_val_476_);
lean_dec_ref(v_env_465_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_array_get_size(v___x_479_);
v___x_482_ = lean_nat_dec_lt(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v___x_479_);
lean_dec(v_tac_466_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_sub(v___x_481_, v___x_484_);
v___x_486_ = lean_nat_dec_le(v___x_480_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v___x_485_);
lean_dec_ref(v___x_479_);
lean_dec(v_tac_466_);
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_tac_466_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v___x_479_, v___x_489_, v___x_480_, v___x_485_);
lean_dec_ref_known(v___x_489_, 2);
lean_dec_ref(v___x_479_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_val_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_500_; 
v_val_492_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_500_ == 0)
{
v___x_494_ = v___x_490_;
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_val_492_);
lean_dec(v___x_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_snd_496_; lean_object* v___x_498_; 
v_snd_496_ = lean_ctor_get(v_val_492_, 1);
lean_inc(v_snd_496_);
lean_dec(v_val_492_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_snd_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_snd_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(lean_object* v_as_501_, lean_object* v_k_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_501_, v_k_502_, v_x_503_, v_x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___boxed(lean_object* v_as_507_, lean_object* v_k_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(v_as_507_, v_k_508_, v_x_509_, v_x_510_, v_x_511_);
lean_dec_ref(v_k_508_);
lean_dec_ref(v_as_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0(lean_object* v_toPure_513_, lean_object* v_____do__lift_514_){
_start:
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_ctor_get(v_____do__lift_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v_____do__lift_514_);
v___x_516_ = lean_apply_2(v_toPure_513_, lean_box(0), v_a_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(lean_object* v_tac_517_, lean_object* v_toPure_518_, lean_object* v_a_519_, lean_object* v_b_520_, lean_object* v_c_521_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_name_eq(v_b_520_, v_tac_517_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v_a_519_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_c_521_);
v___x_524_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = l_Lean_NameSet_insert(v_c_521_, v_a_519_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_apply_2(v_toPure_518_, lean_box(0), v___x_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed(lean_object* v_tac_528_, lean_object* v_toPure_529_, lean_object* v_a_530_, lean_object* v_b_531_, lean_object* v_c_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(v_tac_528_, v_toPure_529_, v_a_530_, v_b_531_, v_c_532_);
lean_dec(v_b_531_);
lean_dec(v_tac_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(lean_object* v_tac_534_, lean_object* v_toPure_535_, lean_object* v_a_536_, lean_object* v_x_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; uint8_t v___x_541_; 
v_fst_539_ = lean_ctor_get(v_a_536_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v_a_536_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v_a_536_);
v___x_541_ = lean_name_eq(v_snd_540_, v_tac_534_);
lean_dec(v_snd_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_fst_539_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___y_538_);
v___x_543_ = lean_apply_2(v_toPure_535_, lean_box(0), v___x_542_);
return v___x_543_;
}
else
{
lean_object* v_found_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_found_544_ = l_Lean_NameSet_insert(v___y_538_, v_fst_539_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_found_544_);
v___x_546_ = lean_apply_2(v_toPure_535_, lean_box(0), v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed(lean_object* v_tac_547_, lean_object* v_toPure_548_, lean_object* v_a_549_, lean_object* v_x_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(v_tac_547_, v_toPure_548_, v_a_549_, v_x_550_, v___y_551_);
lean_dec(v_tac_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3(lean_object* v_toPure_553_, lean_object* v_____s_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_____s_554_);
v___x_556_ = lean_apply_2(v_toPure_553_, lean_box(0), v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4(lean_object* v_inst_557_, lean_object* v___f_558_, lean_object* v_toBind_559_, lean_object* v___f_560_, lean_object* v_a_561_, lean_object* v_x_562_, lean_object* v___y_563_){
_start:
{
size_t v_sz_564_; size_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_sz_564_ = lean_array_size(v_a_561_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_557_, v_a_561_, v___f_558_, v_sz_564_, v___x_565_, v___y_563_);
v___x_567_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v___x_566_, v___f_560_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5(lean_object* v_toPure_568_, lean_object* v_____s_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_apply_2(v_toPure_568_, lean_box(0), v_____s_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object* v___x_571_, lean_object* v_toEnvExtension_572_, lean_object* v_env_573_, lean_object* v_asyncMode_574_, lean_object* v___x_575_, uint8_t v___x_576_, lean_object* v_inst_577_, lean_object* v___f_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v_____s_581_){
_start:
{
lean_object* v___x_582_; lean_object* v_importedEntries_583_; size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_582_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_571_, v_toEnvExtension_572_, v_env_573_, v_asyncMode_574_, v___x_575_, v___x_576_);
v_importedEntries_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref(v_importedEntries_583_);
lean_dec(v___x_582_);
v_sz_584_ = lean_array_size(v_importedEntries_583_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_577_, v_importedEntries_583_, v___f_578_, v_sz_584_, v___x_585_, v_____s_581_);
v___x_587_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_586_, v___f_580_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object* v___x_588_, lean_object* v_toEnvExtension_589_, lean_object* v_env_590_, lean_object* v_asyncMode_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v_inst_594_, lean_object* v___f_595_, lean_object* v_toBind_596_, lean_object* v___f_597_, lean_object* v_____s_598_){
_start:
{
uint8_t v___x_355__boxed_599_; lean_object* v_res_600_; 
v___x_355__boxed_599_ = lean_unbox(v___x_593_);
v_res_600_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(v___x_588_, v_toEnvExtension_589_, v_env_590_, v_asyncMode_591_, v___x_592_, v___x_355__boxed_599_, v_inst_594_, v___f_595_, v_toBind_596_, v___f_597_, v_____s_598_);
lean_dec(v_asyncMode_591_);
lean_dec_ref(v_toEnvExtension_589_);
lean_dec_ref(v___x_588_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object* v___x_601_, lean_object* v_inst_602_, lean_object* v___f_603_, lean_object* v_toBind_604_, lean_object* v___f_605_, lean_object* v___x_606_, lean_object* v___f_607_, lean_object* v___f_608_, lean_object* v_env_609_){
_start:
{
lean_object* v___x_610_; lean_object* v_toEnvExtension_611_; lean_object* v_asyncMode_612_; lean_object* v_found_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_610_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_611_ = lean_ctor_get(v___x_610_, 0);
v_asyncMode_612_ = lean_ctor_get(v_toEnvExtension_611_, 2);
v_found_613_ = l_Lean_NameSet_empty;
v___x_614_ = lean_box(0);
v___x_615_ = 0;
v___x_616_ = lean_box(v___x_615_);
lean_inc_n(v_toBind_604_, 2);
lean_inc_ref(v_inst_602_);
lean_inc(v_asyncMode_612_);
lean_inc_ref(v_env_609_);
lean_inc_ref(v_toEnvExtension_611_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_617_, 0, v___x_601_);
lean_closure_set(v___f_617_, 1, v_toEnvExtension_611_);
lean_closure_set(v___f_617_, 2, v_env_609_);
lean_closure_set(v___f_617_, 3, v_asyncMode_612_);
lean_closure_set(v___f_617_, 4, v___x_614_);
lean_closure_set(v___f_617_, 5, v___x_616_);
lean_closure_set(v___f_617_, 6, v_inst_602_);
lean_closure_set(v___f_617_, 7, v___f_603_);
lean_closure_set(v___f_617_, 8, v_toBind_604_);
lean_closure_set(v___f_617_, 9, v___f_605_);
v___x_618_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_606_, v___x_610_, v_env_609_, v_asyncMode_612_, v___x_614_, v___x_615_);
v___x_619_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_602_, v___f_607_, v_found_613_, v___x_618_);
v___x_620_ = lean_apply_4(v_toBind_604_, lean_box(0), lean_box(0), v___x_619_, v___f_608_);
v___x_621_ = lean_apply_4(v_toBind_604_, lean_box(0), lean_box(0), v___x_620_, v___f_617_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(1);
v___x_623_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_tac_626_){
_start:
{
lean_object* v_toApplicative_627_; lean_object* v_toBind_628_; lean_object* v_getEnv_629_; lean_object* v_toPure_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___x_640_; 
v_toApplicative_627_ = lean_ctor_get(v_inst_624_, 0);
v_toBind_628_ = lean_ctor_get(v_inst_624_, 1);
lean_inc_n(v_toBind_628_, 3);
v_getEnv_629_ = lean_ctor_get(v_inst_625_, 0);
lean_inc(v_getEnv_629_);
lean_dec_ref(v_inst_625_);
v_toPure_630_ = lean_ctor_get(v_toApplicative_627_, 1);
v___x_631_ = lean_box(1);
v___x_632_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_630_, 5);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_633_, 0, v_toPure_630_);
lean_inc(v_tac_626_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_634_, 0, v_tac_626_);
lean_closure_set(v___f_634_, 1, v_toPure_630_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_635_, 0, v_tac_626_);
lean_closure_set(v___f_635_, 1, v_toPure_630_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_636_, 0, v_toPure_630_);
lean_inc_ref(v_inst_624_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4), 7, 4);
lean_closure_set(v___f_637_, 0, v_inst_624_);
lean_closure_set(v___f_637_, 1, v___f_635_);
lean_closure_set(v___f_637_, 2, v_toBind_628_);
lean_closure_set(v___f_637_, 3, v___f_636_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5), 2, 1);
lean_closure_set(v___f_638_, 0, v_toPure_630_);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7), 9, 8);
lean_closure_set(v___f_639_, 0, v___x_632_);
lean_closure_set(v___f_639_, 1, v_inst_624_);
lean_closure_set(v___f_639_, 2, v___f_637_);
lean_closure_set(v___f_639_, 3, v_toBind_628_);
lean_closure_set(v___f_639_, 4, v___f_638_);
lean_closure_set(v___f_639_, 5, v___x_631_);
lean_closure_set(v___f_639_, 6, v___f_634_);
lean_closure_set(v___f_639_, 7, v___f_633_);
v___x_640_ = lean_apply_4(v_toBind_628_, lean_box(0), lean_box(0), v_getEnv_629_, v___f_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object* v_m_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_tac_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Parser_Tactic_Doc_aliases___redArg(v_inst_642_, v_inst_643_, v_tac_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_646_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v___x_651_);
lean_ctor_set(v___x_652_, 3, v___x_651_);
lean_ctor_set(v___x_652_, 4, v___x_650_);
lean_ctor_set(v___x_652_, 5, v___x_650_);
lean_ctor_set(v___x_652_, 6, v___x_650_);
lean_ctor_set(v___x_652_, 7, v___x_650_);
lean_ctor_set(v___x_652_, 8, v___x_650_);
lean_ctor_set(v___x_652_, 9, v___x_650_);
lean_ctor_set(v___x_652_, 10, v___x_650_);
lean_ctor_set(v___x_652_, 11, v___x_649_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(32u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_unsigned_to_nat(32u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_661_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_657_);
lean_ctor_set(v___x_661_, 3, v___x_657_);
lean_ctor_set_usize(v___x_661_, 4, v___x_656_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_box(1);
v___x_663_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_664_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_toCold_671_; lean_object* v_env_672_; lean_object* v_options_673_; uint8_t v___x_674_; lean_object* v_env_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_toCold_671_ = lean_ctor_get(v___y_667_, 0);
v_env_672_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_env_672_);
lean_dec(v___x_670_);
v_options_673_ = lean_ctor_get(v_toCold_671_, 2);
v___x_674_ = 0;
v_env_675_ = l_Lean_Environment_setRecordingDeps(v_env_672_, v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_677_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_673_);
v___x_678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_678_, 0, v_env_675_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
lean_ctor_set(v___x_678_, 3, v_options_673_);
v___x_679_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_msgData_666_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(v_msgData_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_ref_690_; lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_ref_690_ = lean_ctor_get(v___y_687_, 2);
v___x_691_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(v_msg_686_, v___y_687_, v___y_688_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_inc(v_ref_690_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_ref_690_);
lean_ctor_set(v___x_696_, 1, v_a_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 1);
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v_msg_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_705_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object* v_name_712_, lean_object* v_decl_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_717_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_718_ = l_Lean_MessageData_ofName(v_name_712_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_721_, v___y_714_, v___y_715_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object* v_name_723_, lean_object* v_decl_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(v_name_723_, v_decl_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v_decl_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object* v_addEntryFn_729_, lean_object* v___x_730_, lean_object* v_s_731_){
_start:
{
lean_object* v_importedEntries_732_; lean_object* v_state_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_importedEntries_732_ = lean_ctor_get(v_s_731_, 0);
v_state_733_ = lean_ctor_get(v_s_731_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_s_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v_s_731_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_state_733_);
lean_inc(v_importedEntries_732_);
lean_dec(v_s_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_state_737_; lean_object* v___x_739_; 
v_state_737_ = lean_apply_2(v_addEntryFn_729_, v_state_733_, v___x_730_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_state_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_importedEntries_732_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_state_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1(size_t v_sz_745_, size_t v_i_746_, lean_object* v_bs_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_748_ == 0)
{
return v_bs_747_;
}
else
{
lean_object* v_v_749_; lean_object* v___x_750_; lean_object* v_bs_x27_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_v_749_ = lean_array_uget(v_bs_747_, v_i_746_);
v___x_750_ = lean_unsigned_to_nat(0u);
v_bs_x27_751_ = lean_array_uset(v_bs_747_, v_i_746_, v___x_750_);
v___x_752_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_753_ = l_Lean_MessageData_ofName(v_v_749_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_752_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_746_, v___x_756_);
v___x_758_ = lean_array_uset(v_bs_x27_751_, v_i_746_, v___x_755_);
v_i_746_ = v___x_757_;
v_bs_747_ = v___x_758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(uint8_t v___x_766_, lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_eq(v_i_768_, v_stop_769_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_array_uget_borrowed(v_as_767_, v_i_768_);
v___x_776_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_777_ = lean_name_eq(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
goto v___jp_770_;
}
else
{
if (v___x_766_ == 0)
{
goto v___jp_770_;
}
else
{
return v___x_766_;
}
}
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
v___jp_770_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_768_, v___x_771_);
v_i_768_ = v___x_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2___boxed(lean_object* v___x_779_, lean_object* v_as_780_, lean_object* v_i_781_, lean_object* v_stop_782_){
_start:
{
uint8_t v___x_8635__boxed_783_; size_t v_i_boxed_784_; size_t v_stop_boxed_785_; uint8_t v_res_786_; lean_object* v_r_787_; 
v___x_8635__boxed_783_ = lean_unbox(v___x_779_);
v_i_boxed_784_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_782_);
lean_dec(v_stop_782_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(v___x_8635__boxed_783_, v_as_780_, v_i_boxed_784_, v_stop_boxed_785_);
lean_dec_ref(v_as_780_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(lean_object* v_ref_788_, lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_toCold_793_; lean_object* v_currRecDepth_794_; lean_object* v_ref_795_; uint16_t v_optionFlags_796_; uint8_t v_suppressElabErrors_797_; uint8_t v_checkDeprecated_798_; uint8_t v_isRecordingDeps_799_; lean_object* v_ref_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_toCold_793_ = lean_ctor_get(v___y_790_, 0);
v_currRecDepth_794_ = lean_ctor_get(v___y_790_, 1);
v_ref_795_ = lean_ctor_get(v___y_790_, 2);
v_optionFlags_796_ = lean_ctor_get_uint16(v___y_790_, sizeof(void*)*3);
v_suppressElabErrors_797_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 2);
v_checkDeprecated_798_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 3);
v_isRecordingDeps_799_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 4);
v_ref_800_ = l_Lean_replaceRef(v_ref_788_, v_ref_795_);
lean_inc(v_currRecDepth_794_);
lean_inc_ref(v_toCold_793_);
v___x_801_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_801_, 0, v_toCold_793_);
lean_ctor_set(v___x_801_, 1, v_currRecDepth_794_);
lean_ctor_set(v___x_801_, 2, v_ref_800_);
lean_ctor_set_uint16(v___x_801_, sizeof(void*)*3, v_optionFlags_796_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*3 + 2, v_suppressElabErrors_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*3 + 3, v_checkDeprecated_798_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*3 + 4, v_isRecordingDeps_799_);
v___x_802_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v_msg_789_, v___x_801_, v___y_791_);
lean_dec_ref_known(v___x_801_, 3);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_ref_803_, v_msg_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_ref_803_);
return v_res_808_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__0));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__2));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__4));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(lean_object* v_attrName_818_, lean_object* v_declName_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_823_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1);
v___x_824_ = l_Lean_MessageData_ofName(v_attrName_818_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = 0;
v___x_829_ = l_Lean_MessageData_ofConstName(v_declName_819_, v___x_828_);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_827_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_832_, v___y_820_, v___y_821_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_attrName_834_, lean_object* v_declName_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_attrName_834_, v_declName_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_839_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(lean_object* v_name_849_, uint8_t v_kind_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___y_860_; 
v___x_854_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_855_ = l_Lean_MessageData_ofName(v_name_849_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
switch(v_kind_850_)
{
case 0:
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___y_860_ = v___x_867_;
goto v___jp_859_;
}
case 1:
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__5));
v___y_860_ = v___x_868_;
goto v___jp_859_;
}
default: 
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__6));
v___y_860_ = v___x_869_;
goto v___jp_859_;
}
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_inc_ref(v___y_860_);
v___x_861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_861_, 0, v___y_860_);
v___x_862_ = l_Lean_MessageData_ofFormat(v___x_861_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_858_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_865_, v___y_851_, v___y_852_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_name_870_, lean_object* v_kind_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_kind_boxed_875_; lean_object* v_res_876_; 
v_kind_boxed_875_ = lean_unbox(v_kind_871_);
v_res_876_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_870_, v_kind_boxed_875_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
return v___x_879_;
}
else
{
lean_object* v_key_880_; lean_object* v_value_881_; lean_object* v_tail_882_; uint8_t v___x_883_; 
v_key_880_ = lean_ctor_get(v_x_878_, 0);
v_value_881_ = lean_ctor_get(v_x_878_, 1);
v_tail_882_ = lean_ctor_get(v_x_878_, 2);
v___x_883_ = lean_name_eq(v_key_880_, v_a_877_);
if (v___x_883_ == 0)
{
v_x_878_ = v_tail_882_;
goto _start;
}
else
{
lean_object* v___x_885_; 
lean_inc(v_value_881_);
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_value_881_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec(v_a_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_m_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_buckets_891_; lean_object* v___x_892_; uint64_t v___y_894_; 
v_buckets_891_ = lean_ctor_get(v_m_889_, 1);
v___x_892_ = lean_array_get_size(v_buckets_891_);
if (lean_obj_tag(v_a_890_) == 0)
{
uint64_t v___x_908_; 
v___x_908_ = 1723ULL;
v___y_894_ = v___x_908_;
goto v___jp_893_;
}
else
{
uint64_t v_hash_909_; 
v_hash_909_ = lean_ctor_get_uint64(v_a_890_, sizeof(void*)*2);
v___y_894_ = v_hash_909_;
goto v___jp_893_;
}
v___jp_893_:
{
uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v_fold_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_895_ = 32ULL;
v___x_896_ = lean_uint64_shift_right(v___y_894_, v___x_895_);
v_fold_897_ = lean_uint64_xor(v___y_894_, v___x_896_);
v___x_898_ = 16ULL;
v___x_899_ = lean_uint64_shift_right(v_fold_897_, v___x_898_);
v___x_900_ = lean_uint64_xor(v_fold_897_, v___x_899_);
v___x_901_ = lean_uint64_to_usize(v___x_900_);
v___x_902_ = lean_usize_of_nat(v___x_892_);
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_sub(v___x_902_, v___x_903_);
v___x_905_ = lean_usize_land(v___x_901_, v___x_904_);
v___x_906_ = lean_array_uget_borrowed(v_buckets_891_, v___x_905_);
v___x_907_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_890_, v___x_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v_m_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_m_910_);
return v_res_912_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_913_; double v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_float_of_nat(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object* v_cls_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_ref_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_970_; 
v_ref_923_ = lean_ctor_get(v___y_920_, 2);
v___x_924_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(v_msg_919_, v___y_920_, v___y_921_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_970_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_970_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_970_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v_traceState_930_; lean_object* v_env_931_; lean_object* v_nextMacroScope_932_; lean_object* v_ngen_933_; lean_object* v_auxDeclNGen_934_; lean_object* v_cache_935_; lean_object* v_recordedDeps_936_; lean_object* v_messages_937_; lean_object* v_infoState_938_; lean_object* v_snapshotTasks_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_969_; 
v___x_929_ = lean_st_ref_take(v___y_921_);
v_traceState_930_ = lean_ctor_get(v___x_929_, 4);
v_env_931_ = lean_ctor_get(v___x_929_, 0);
v_nextMacroScope_932_ = lean_ctor_get(v___x_929_, 1);
v_ngen_933_ = lean_ctor_get(v___x_929_, 2);
v_auxDeclNGen_934_ = lean_ctor_get(v___x_929_, 3);
v_cache_935_ = lean_ctor_get(v___x_929_, 5);
v_recordedDeps_936_ = lean_ctor_get(v___x_929_, 6);
v_messages_937_ = lean_ctor_get(v___x_929_, 7);
v_infoState_938_ = lean_ctor_get(v___x_929_, 8);
v_snapshotTasks_939_ = lean_ctor_get(v___x_929_, 9);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_969_ == 0)
{
v___x_941_ = v___x_929_;
v_isShared_942_ = v_isSharedCheck_969_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snapshotTasks_939_);
lean_inc(v_infoState_938_);
lean_inc(v_messages_937_);
lean_inc(v_recordedDeps_936_);
lean_inc(v_cache_935_);
lean_inc(v_traceState_930_);
lean_inc(v_auxDeclNGen_934_);
lean_inc(v_ngen_933_);
lean_inc(v_nextMacroScope_932_);
lean_inc(v_env_931_);
lean_dec(v___x_929_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_969_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
uint64_t v_tid_943_; lean_object* v_traces_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_968_; 
v_tid_943_ = lean_ctor_get_uint64(v_traceState_930_, sizeof(void*)*1);
v_traces_944_ = lean_ctor_get(v_traceState_930_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_traceState_930_);
if (v_isSharedCheck_968_ == 0)
{
v___x_946_ = v_traceState_930_;
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_traces_944_);
lean_dec(v_traceState_930_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; double v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_948_ = lean_box(0);
v___x_949_ = lean_box(0);
v___x_950_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0);
v___x_951_ = 0;
v___x_952_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_953_, 0, v_cls_918_);
lean_ctor_set(v___x_953_, 1, v___x_949_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
lean_ctor_set_float(v___x_953_, sizeof(void*)*3, v___x_950_);
lean_ctor_set_float(v___x_953_, sizeof(void*)*3 + 8, v___x_950_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*3 + 16, v___x_951_);
v___x_954_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__2));
v___x_955_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v_a_925_);
lean_ctor_set(v___x_955_, 2, v___x_954_);
lean_inc(v_ref_923_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_ref_923_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_PersistentArray_push___redArg(v_traces_944_, v___x_956_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_957_);
v___x_959_ = v___x_946_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_957_);
lean_ctor_set_uint64(v_reuseFailAlloc_967_, sizeof(void*)*1, v_tid_943_);
v___x_959_ = v_reuseFailAlloc_967_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 4, v___x_959_);
v___x_961_ = v___x_941_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_env_931_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_nextMacroScope_932_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_ngen_933_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_auxDeclNGen_934_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_cache_935_);
lean_ctor_set(v_reuseFailAlloc_966_, 6, v_recordedDeps_936_);
lean_ctor_set(v_reuseFailAlloc_966_, 7, v_messages_937_);
lean_ctor_set(v_reuseFailAlloc_966_, 8, v_infoState_938_);
lean_ctor_set(v_reuseFailAlloc_966_, 9, v_snapshotTasks_939_);
v___x_961_ = v_reuseFailAlloc_966_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_st_ref_put(v___y_921_, v___x_961_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_948_);
v___x_964_ = v___x_927_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_948_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___boxed(lean_object* v_cls_971_, lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(v_cls_971_, v_msg_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___lam__0(lean_object* v___x_977_, lean_object* v_entry_978_, lean_object* v_s_979_){
_start:
{
lean_object* v_addEntryFn_980_; lean_object* v_importedEntries_981_; lean_object* v_state_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_addEntryFn_980_ = lean_ctor_get(v___x_977_, 3);
lean_inc(v_addEntryFn_980_);
lean_dec_ref(v___x_977_);
v_importedEntries_981_ = lean_ctor_get(v_s_979_, 0);
v_state_982_ = lean_ctor_get(v_s_979_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_s_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v_s_979_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_state_982_);
lean_inc(v_importedEntries_981_);
lean_dec(v_s_979_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_state_986_; lean_object* v___x_988_; 
v_state_986_ = lean_apply_2(v_addEntryFn_980_, v_state_982_, v_entry_978_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v_state_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_importedEntries_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_state_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(lean_object* v_keys_991_, lean_object* v_i_992_, lean_object* v_k_993_){
_start:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_array_get_size(v_keys_991_);
v___x_995_ = lean_nat_dec_lt(v_i_992_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec(v_i_992_);
return v___x_995_;
}
else
{
lean_object* v_k_x27_996_; uint8_t v___x_997_; 
v_k_x27_996_ = lean_array_fget_borrowed(v_keys_991_, v_i_992_);
v___x_997_ = l_Lean_instBEqExtraModUse_beq(v_k_993_, v_k_x27_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_add(v_i_992_, v___x_998_);
lean_dec(v_i_992_);
v_i_992_ = v___x_999_;
goto _start;
}
else
{
lean_dec(v_i_992_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_keys_1001_, lean_object* v_i_1002_, lean_object* v_k_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_keys_1001_, v_i_1002_, v_k_1003_);
lean_dec_ref(v_k_1003_);
lean_dec_ref(v_keys_1001_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(lean_object* v_x_1006_, size_t v_x_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_es_1009_; lean_object* v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; lean_object* v_j_1013_; lean_object* v___x_1014_; 
v_es_1009_ = lean_ctor_get(v_x_1006_, 0);
v___x_1010_ = lean_box(2);
v___x_1011_ = ((size_t)31ULL);
v___x_1012_ = lean_usize_land(v_x_1007_, v___x_1011_);
v_j_1013_ = lean_usize_to_nat(v___x_1012_);
v___x_1014_ = lean_array_get_borrowed(v___x_1010_, v_es_1009_, v_j_1013_);
lean_dec(v_j_1013_);
switch(lean_obj_tag(v___x_1014_))
{
case 0:
{
lean_object* v_key_1015_; uint8_t v___x_1016_; 
v_key_1015_ = lean_ctor_get(v___x_1014_, 0);
v___x_1016_ = l_Lean_instBEqExtraModUse_beq(v_x_1008_, v_key_1015_);
return v___x_1016_;
}
case 1:
{
lean_object* v_node_1017_; size_t v___x_1018_; size_t v___x_1019_; 
v_node_1017_ = lean_ctor_get(v___x_1014_, 0);
v___x_1018_ = ((size_t)5ULL);
v___x_1019_ = lean_usize_shift_right(v_x_1007_, v___x_1018_);
v_x_1006_ = v_node_1017_;
v_x_1007_ = v___x_1019_;
goto _start;
}
default: 
{
uint8_t v___x_1021_; 
v___x_1021_ = 0;
return v___x_1021_;
}
}
}
else
{
lean_object* v_ks_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_ks_1022_ = lean_ctor_get(v_x_1006_, 0);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_ks_1022_, v___x_1023_, v_x_1008_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
size_t v_x_8975__boxed_1028_; uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_x_8975__boxed_1028_ = lean_unbox_usize(v_x_1026_);
lean_dec(v_x_1026_);
v_res_1029_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1025_, v_x_8975__boxed_1028_, v_x_1027_);
lean_dec_ref(v_x_1027_);
lean_dec_ref(v_x_1025_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
uint64_t v___x_1033_; size_t v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = l_Lean_instHashableExtraModUse_hash(v_x_1032_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1031_, v___x_1034_, v_x_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_x_1036_, v_x_1037_);
lean_dec_ref(v_x_1037_);
lean_dec_ref(v_x_1036_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__5));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__7));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_cls_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4));
v___x_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__11));
v___x_1061_ = l_Lean_Name_append(v___x_1060_, v_cls_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__13));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__15));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_mod_1072_, uint8_t v_isMeta_1073_, lean_object* v_hint_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_env_1096_; uint8_t v_isExporting_1097_; lean_object* v_entry_1098_; lean_object* v___x_1099_; lean_object* v_env_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2);
v___x_1095_ = lean_st_ref_get(v___y_1076_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v_isExporting_1097_ = lean_ctor_get_uint8(v_env_1096_, sizeof(void*)*13);
lean_dec_ref(v_env_1096_);
lean_inc(v_mod_1072_);
v_entry_1098_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1098_, 0, v_mod_1072_);
lean_ctor_set_uint8(v_entry_1098_, sizeof(void*)*1, v_isExporting_1097_);
lean_ctor_set_uint8(v_entry_1098_, sizeof(void*)*1 + 1, v_isMeta_1073_);
v___x_1099_ = lean_st_ref_get(v___y_1076_);
v_env_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_env_1100_);
lean_dec(v___x_1099_);
v___x_1101_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1102_ = lean_box(1);
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1094_, v___x_1101_, v_env_1100_, v___x_1102_, v___x_1103_);
v___x_1105_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v___x_1104_, v_entry_1098_);
lean_dec(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v_toCold_1106_; lean_object* v_options_1107_; lean_object* v_inheritedTraceOptions_1108_; uint8_t v_hasTrace_1109_; lean_object* v___f_1110_; uint8_t v___x_1111_; lean_object* v___y_1113_; 
v_toCold_1106_ = lean_ctor_get(v___y_1075_, 0);
v_options_1107_ = lean_ctor_get(v_toCold_1106_, 2);
v_inheritedTraceOptions_1108_ = lean_ctor_get(v_toCold_1106_, 11);
v_hasTrace_1109_ = lean_ctor_get_uint8(v_options_1107_, sizeof(void*)*1);
v___f_1110_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_1110_, 0, v___x_1101_);
lean_closure_set(v___f_1110_, 1, v_entry_1098_);
v___x_1111_ = 1;
if (v_hasTrace_1109_ == 0)
{
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
lean_object* v_cls_1131_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_cls_1131_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4));
v___x_1151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12);
v___x_1152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1108_, v_options_1107_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1153_; lean_object* v___y_1155_; 
v___x_1153_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14);
if (v_isExporting_1097_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__19));
v___y_1155_ = v___x_1162_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__20));
v___y_1155_ = v___x_1163_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_ref(v___y_1155_);
v___x_1156_ = l_Lean_stringToMessageData(v___y_1155_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1153_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
if (v_isMeta_1073_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__17));
v___y_1138_ = v___x_1159_;
v___y_1139_ = v___x_1160_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__18));
v___y_1138_ = v___x_1159_;
v___y_1139_ = v___x_1161_;
goto v___jp_1137_;
}
}
}
v___jp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1133_);
lean_ctor_set(v___x_1135_, 1, v___y_1134_);
v___x_1136_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(v_cls_1131_, v___x_1135_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref_known(v___x_1136_, 1);
v___y_1113_ = v___y_1076_;
goto v___jp_1112_;
}
else
{
lean_dec_ref(v___f_1110_);
return v___x_1136_;
}
}
v___jp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
lean_inc_ref(v___y_1139_);
v___x_1140_ = l_Lean_stringToMessageData(v___y_1139_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1138_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_ofName(v_mod_1072_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_Name_isAnonymous(v_hint_1074_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8);
v___x_1148_ = l_Lean_MessageData_ofName(v_hint_1074_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___y_1133_ = v___x_1145_;
v___y_1134_ = v___x_1149_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1150_; 
lean_dec(v_hint_1074_);
v___x_1150_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9);
v___y_1133_ = v___x_1145_;
v___y_1134_ = v___x_1150_;
goto v___jp_1132_;
}
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v_toEnvExtension_1115_; lean_object* v_env_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_ngen_1118_; lean_object* v_auxDeclNGen_1119_; lean_object* v_traceState_1120_; lean_object* v_recordedDeps_1121_; lean_object* v_messages_1122_; lean_object* v_infoState_1123_; lean_object* v_snapshotTasks_1124_; lean_object* v_asyncMode_1125_; uint8_t v_logWrites_1126_; lean_object* v___x_1127_; 
v___x_1114_ = lean_st_ref_take(v___y_1113_);
v_toEnvExtension_1115_ = lean_ctor_get(v___x_1101_, 0);
v_env_1116_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1116_);
v_nextMacroScope_1117_ = lean_ctor_get(v___x_1114_, 1);
lean_inc(v_nextMacroScope_1117_);
v_ngen_1118_ = lean_ctor_get(v___x_1114_, 2);
lean_inc_ref(v_ngen_1118_);
v_auxDeclNGen_1119_ = lean_ctor_get(v___x_1114_, 3);
lean_inc_ref(v_auxDeclNGen_1119_);
v_traceState_1120_ = lean_ctor_get(v___x_1114_, 4);
lean_inc_ref(v_traceState_1120_);
v_recordedDeps_1121_ = lean_ctor_get(v___x_1114_, 6);
lean_inc_ref(v_recordedDeps_1121_);
v_messages_1122_ = lean_ctor_get(v___x_1114_, 7);
lean_inc_ref(v_messages_1122_);
v_infoState_1123_ = lean_ctor_get(v___x_1114_, 8);
lean_inc_ref(v_infoState_1123_);
v_snapshotTasks_1124_ = lean_ctor_get(v___x_1114_, 9);
lean_inc_ref(v_snapshotTasks_1124_);
lean_dec(v___x_1114_);
v_asyncMode_1125_ = lean_ctor_get(v_toEnvExtension_1115_, 2);
v_logWrites_1126_ = lean_ctor_get_uint8(v_toEnvExtension_1115_, sizeof(void*)*6);
v___x_1127_ = lean_box(0);
if (v_logWrites_1126_ == 0)
{
lean_object* v___x_1128_; 
lean_inc_ref(v_toEnvExtension_1115_);
v___x_1128_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1115_, v_env_1116_, v___f_1110_, v_asyncMode_1125_, v___x_1103_, v___x_1111_);
v___y_1079_ = v_ngen_1118_;
v___y_1080_ = v_messages_1122_;
v___y_1081_ = v___y_1113_;
v___y_1082_ = v_snapshotTasks_1124_;
v___y_1083_ = v_recordedDeps_1121_;
v___y_1084_ = v_nextMacroScope_1117_;
v___y_1085_ = v_infoState_1123_;
v___y_1086_ = v_auxDeclNGen_1119_;
v___y_1087_ = v_traceState_1120_;
v___y_1088_ = v___x_1127_;
v___y_1089_ = v___x_1128_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc_ref_n(v_toEnvExtension_1115_, 2);
v___x_1129_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1115_, v_env_1116_);
lean_dec_ref(v_env_1116_);
v___x_1130_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1115_, v___x_1129_, v___f_1110_, v_asyncMode_1125_, v___x_1103_, v___x_1111_);
v___y_1079_ = v_ngen_1118_;
v___y_1080_ = v_messages_1122_;
v___y_1081_ = v___y_1113_;
v___y_1082_ = v_snapshotTasks_1124_;
v___y_1083_ = v_recordedDeps_1121_;
v___y_1084_ = v_nextMacroScope_1117_;
v___y_1085_ = v_infoState_1123_;
v___y_1086_ = v_auxDeclNGen_1119_;
v___y_1087_ = v_traceState_1120_;
v___y_1088_ = v___x_1127_;
v___y_1089_ = v___x_1130_;
goto v___jp_1078_;
}
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref_known(v_entry_1098_, 1);
lean_dec(v_hint_1074_);
lean_dec(v_mod_1072_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
v___jp_1078_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_1091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1089_);
lean_ctor_set(v___x_1091_, 1, v___y_1084_);
lean_ctor_set(v___x_1091_, 2, v___y_1079_);
lean_ctor_set(v___x_1091_, 3, v___y_1086_);
lean_ctor_set(v___x_1091_, 4, v___y_1087_);
lean_ctor_set(v___x_1091_, 5, v___x_1090_);
lean_ctor_set(v___x_1091_, 6, v___y_1083_);
lean_ctor_set(v___x_1091_, 7, v___y_1080_);
lean_ctor_set(v___x_1091_, 8, v___y_1085_);
lean_ctor_set(v___x_1091_, 9, v___y_1082_);
v___x_1092_ = lean_st_ref_put(v___y_1081_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1088_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_mod_1166_, lean_object* v_isMeta_1167_, lean_object* v_hint_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_isMeta_boxed_1172_; lean_object* v_res_1173_; 
v_isMeta_boxed_1172_ = lean_unbox(v_isMeta_1167_);
v_res_1173_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_mod_1166_, v_isMeta_boxed_1172_, v_hint_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(lean_object* v___x_1174_, lean_object* v_declName_1175_, lean_object* v_as_1176_, size_t v_sz_1177_, size_t v_i_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1178_, v_sz_1177_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_dec(v_declName_1175_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1179_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v_modules_1186_; lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v_toImport_1190_; lean_object* v_module_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1185_ = l_Lean_Environment_header(v___x_1174_);
v_modules_1186_ = lean_ctor_get(v___x_1185_, 3);
lean_inc_ref(v_modules_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1188_ = lean_array_uget_borrowed(v_as_1176_, v_i_1178_);
v___x_1189_ = lean_array_get(v___x_1187_, v_modules_1186_, v_a_1188_);
lean_dec_ref(v_modules_1186_);
v_toImport_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_toImport_1190_);
lean_dec(v___x_1189_);
v_module_1191_ = lean_ctor_get(v_toImport_1190_, 0);
lean_inc(v_module_1191_);
lean_dec_ref(v_toImport_1190_);
v___x_1192_ = lean_box(0);
v___x_1193_ = 0;
lean_inc(v_declName_1175_);
v___x_1194_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_module_1191_, v___x_1193_, v_declName_1175_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1194_) == 0)
{
size_t v___x_1195_; size_t v___x_1196_; 
lean_dec_ref_known(v___x_1194_, 1);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_i_1178_, v___x_1195_);
v_i_1178_ = v___x_1196_;
v_b_1179_ = v___x_1192_;
goto _start;
}
else
{
lean_dec(v_declName_1175_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v___x_1198_, lean_object* v_declName_1199_, lean_object* v_as_1200_, lean_object* v_sz_1201_, lean_object* v_i_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
size_t v_sz_boxed_1207_; size_t v_i_boxed_1208_; lean_object* v_res_1209_; 
v_sz_boxed_1207_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1208_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(v___x_1198_, v_declName_1199_, v_as_1200_, v_sz_boxed_1207_, v_i_boxed_1208_, v_b_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_as_1200_);
lean_dec_ref(v___x_1198_);
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(lean_object* v_declName_1213_, uint8_t v_isMeta_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_env_1223_; lean_object* v___y_1225_; lean_object* v___x_1238_; 
v___x_1218_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0);
v___x_1219_ = lean_st_ref_get(v___y_1216_);
v_env_1223_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1219_);
v___x_1238_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1223_, v_declName_1213_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_dec_ref(v_env_1223_);
lean_dec(v_declName_1213_);
goto v___jp_1220_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; lean_object* v_modules_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_val_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = l_Lean_Environment_header(v_env_1223_);
v_modules_1241_ = lean_ctor_get(v___x_1240_, 3);
lean_inc_ref(v_modules_1241_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_array_get_size(v_modules_1241_);
v___x_1243_ = lean_nat_dec_lt(v_val_1239_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_modules_1241_);
lean_dec(v_val_1239_);
lean_dec_ref(v_env_1223_);
lean_dec(v_declName_1213_);
goto v___jp_1220_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___y_1247_; 
v___x_1244_ = lean_array_fget(v_modules_1241_, v_val_1239_);
lean_dec(v_val_1239_);
lean_dec_ref(v_modules_1241_);
v___x_1245_ = lean_st_ref_get(v___y_1216_);
if (v_isMeta_1214_ == 0)
{
lean_dec(v___x_1245_);
v___y_1247_ = v_isMeta_1214_;
goto v___jp_1246_;
}
else
{
lean_object* v_env_1258_; uint8_t v___x_1259_; 
v_env_1258_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_env_1258_);
lean_dec(v___x_1245_);
lean_inc(v_declName_1213_);
v___x_1259_ = l_Lean_isMarkedMeta(v_env_1258_, v_declName_1213_);
if (v___x_1259_ == 0)
{
v___y_1247_ = v_isMeta_1214_;
goto v___jp_1246_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = 0;
v___y_1247_ = v___x_1260_;
goto v___jp_1246_;
}
}
v___jp_1246_:
{
lean_object* v_toImport_1248_; lean_object* v_module_1249_; lean_object* v___x_1250_; 
v_toImport_1248_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_toImport_1248_);
lean_dec(v___x_1244_);
v_module_1249_ = lean_ctor_get(v_toImport_1248_, 0);
lean_inc(v_module_1249_);
lean_dec_ref(v_toImport_1248_);
lean_inc(v_declName_1213_);
v___x_1250_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_module_1249_, v___y_1247_, v_declName_1213_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref_known(v___x_1250_, 1);
v___x_1251_ = l_Lean_indirectModUseExt;
v___x_1252_ = lean_box(1);
v___x_1253_ = lean_box(0);
lean_inc_ref(v_env_1223_);
v___x_1254_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1218_, v___x_1251_, v_env_1223_, v___x_1252_, v___x_1253_);
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v___x_1254_, v_declName_1213_);
lean_dec(v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__1));
v___y_1225_ = v___x_1256_;
goto v___jp_1224_;
}
else
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1255_, 1);
v___y_1225_ = v_val_1257_;
goto v___jp_1224_;
}
}
else
{
lean_dec_ref(v_env_1223_);
lean_dec(v_declName_1213_);
return v___x_1250_;
}
}
}
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
v___jp_1224_:
{
lean_object* v___x_1226_; size_t v_sz_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_box(0);
v_sz_1227_ = lean_array_size(v___y_1225_);
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(v_env_1223_, v_declName_1213_, v___y_1225_, v_sz_1227_, v___x_1228_, v___x_1226_, v___y_1215_, v___y_1216_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v_env_1223_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1237_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1226_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1226_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1261_, lean_object* v_isMeta_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_isMeta_boxed_1266_; lean_object* v_res_1267_; 
v_isMeta_boxed_1266_ = lean_unbox(v_isMeta_1262_);
v_res_1267_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(v_declName_1261_, v_isMeta_boxed_1266_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1267_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v_name_1298_, lean_object* v_decl_1299_, lean_object* v_stx_1300_, uint8_t v_kind_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___y_1306_; lean_object* v_nextMacroScope_1307_; lean_object* v_ngen_1308_; lean_object* v_auxDeclNGen_1309_; lean_object* v_traceState_1310_; lean_object* v_recordedDeps_1311_; lean_object* v_messages_1312_; lean_object* v_infoState_1313_; lean_object* v_snapshotTasks_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = 0;
v___x_1456_ = l_Lean_instBEqAttributeKind_beq(v_kind_1301_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v_stx_1300_);
lean_dec(v_decl_1299_);
lean_dec_ref(v___x_1297_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v___x_1295_);
lean_dec(v___x_1293_);
v___x_1457_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_1298_, v_kind_1301_, v___y_1302_, v___y_1303_);
return v___x_1457_;
}
else
{
goto v___jp_1450_;
}
v___jp_1305_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_1318_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1318_, 0, v___y_1316_);
lean_ctor_set(v___x_1318_, 1, v_nextMacroScope_1307_);
lean_ctor_set(v___x_1318_, 2, v_ngen_1308_);
lean_ctor_set(v___x_1318_, 3, v_auxDeclNGen_1309_);
lean_ctor_set(v___x_1318_, 4, v_traceState_1310_);
lean_ctor_set(v___x_1318_, 5, v___x_1317_);
lean_ctor_set(v___x_1318_, 6, v_recordedDeps_1311_);
lean_ctor_set(v___x_1318_, 7, v_messages_1312_);
lean_ctor_set(v___x_1318_, 8, v_infoState_1313_);
lean_ctor_set(v___x_1318_, 9, v_snapshotTasks_1314_);
v___x_1319_ = lean_st_ref_put(v___y_1306_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___y_1315_);
return v___x_1320_;
}
v___jp_1321_:
{
lean_object* v___x_1325_; lean_object* v_env_1326_; lean_object* v_nextMacroScope_1327_; lean_object* v_ngen_1328_; lean_object* v_auxDeclNGen_1329_; lean_object* v_traceState_1330_; lean_object* v_recordedDeps_1331_; lean_object* v_messages_1332_; lean_object* v_infoState_1333_; lean_object* v_snapshotTasks_1334_; lean_object* v___x_1335_; lean_object* v_toEnvExtension_1336_; lean_object* v_addEntryFn_1337_; lean_object* v_asyncMode_1338_; uint8_t v_logWrites_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; 
v___x_1325_ = lean_st_ref_take(v___y_1324_);
v_env_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_ref(v_env_1326_);
v_nextMacroScope_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_nextMacroScope_1327_);
v_ngen_1328_ = lean_ctor_get(v___x_1325_, 2);
lean_inc_ref(v_ngen_1328_);
v_auxDeclNGen_1329_ = lean_ctor_get(v___x_1325_, 3);
lean_inc_ref(v_auxDeclNGen_1329_);
v_traceState_1330_ = lean_ctor_get(v___x_1325_, 4);
lean_inc_ref(v_traceState_1330_);
v_recordedDeps_1331_ = lean_ctor_get(v___x_1325_, 6);
lean_inc_ref(v_recordedDeps_1331_);
v_messages_1332_ = lean_ctor_get(v___x_1325_, 7);
lean_inc_ref(v_messages_1332_);
v_infoState_1333_ = lean_ctor_get(v___x_1325_, 8);
lean_inc_ref(v_infoState_1333_);
v_snapshotTasks_1334_ = lean_ctor_get(v___x_1325_, 9);
lean_inc_ref(v_snapshotTasks_1334_);
lean_dec(v___x_1325_);
v___x_1335_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1336_ = lean_ctor_get(v___x_1335_, 0);
v_addEntryFn_1337_ = lean_ctor_get(v___x_1335_, 3);
v_asyncMode_1338_ = lean_ctor_get(v_toEnvExtension_1336_, 2);
v_logWrites_1339_ = lean_ctor_get_uint8(v_toEnvExtension_1336_, sizeof(void*)*6);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_decl_1299_);
lean_ctor_set(v___x_1341_, 1, v___y_1323_);
lean_inc(v_addEntryFn_1337_);
v___f_1342_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1342_, 0, v_addEntryFn_1337_);
lean_closure_set(v___f_1342_, 1, v___x_1341_);
if (v_logWrites_1339_ == 0)
{
lean_object* v___x_1343_; 
lean_inc_ref(v_toEnvExtension_1336_);
v___x_1343_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1336_, v_env_1326_, v___f_1342_, v_asyncMode_1338_, v___x_1293_, v___y_1322_);
v___y_1306_ = v___y_1324_;
v_nextMacroScope_1307_ = v_nextMacroScope_1327_;
v_ngen_1308_ = v_ngen_1328_;
v_auxDeclNGen_1309_ = v_auxDeclNGen_1329_;
v_traceState_1310_ = v_traceState_1330_;
v_recordedDeps_1311_ = v_recordedDeps_1331_;
v_messages_1312_ = v_messages_1332_;
v_infoState_1313_ = v_infoState_1333_;
v_snapshotTasks_1314_ = v_snapshotTasks_1334_;
v___y_1315_ = v___x_1340_;
v___y_1316_ = v___x_1343_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_inc_ref_n(v_toEnvExtension_1336_, 2);
v___x_1344_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1336_, v_env_1326_);
lean_dec_ref(v_env_1326_);
v___x_1345_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1336_, v___x_1344_, v___f_1342_, v_asyncMode_1338_, v___x_1293_, v___y_1322_);
v___y_1306_ = v___y_1324_;
v_nextMacroScope_1307_ = v_nextMacroScope_1327_;
v_ngen_1308_ = v_ngen_1328_;
v_auxDeclNGen_1309_ = v_auxDeclNGen_1329_;
v_traceState_1310_ = v_traceState_1330_;
v_recordedDeps_1311_ = v_recordedDeps_1331_;
v_messages_1312_ = v_messages_1332_;
v_infoState_1313_ = v_infoState_1333_;
v_snapshotTasks_1314_ = v_snapshotTasks_1334_;
v___y_1315_ = v___x_1340_;
v___y_1316_ = v___x_1345_;
goto v___jp_1305_;
}
}
v___jp_1346_:
{
lean_object* v___x_1351_; lean_object* v_env_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_st_ref_get(v___y_1350_);
v_env_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_ref(v_env_1352_);
lean_dec(v___x_1351_);
lean_inc(v___y_1348_);
v___x_1353_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1352_, v___y_1348_);
if (lean_obj_tag(v___x_1353_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_decl_1299_);
lean_dec(v___x_1293_);
v_val_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1356_ = l_Lean_MessageData_ofName(v___y_1348_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_MessageData_ofName(v_val_1354_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___x_1355_);
v___x_1363_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1362_, v___y_1349_, v___y_1350_);
return v___x_1363_;
}
else
{
lean_dec(v___x_1353_);
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1350_;
goto v___jp_1321_;
}
}
v___jp_1364_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v___y_1367_);
v___x_1371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1372_ = l_Lean_MessageData_ofName(v_decl_1299_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
lean_inc_ref(v___y_1370_);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___y_1370_);
v___x_1377_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_array_to_list(v___y_1369_);
v___x_1380_ = l_Lean_MessageData_andList(v___x_1379_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1378_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1383_, v___y_1365_, v___y_1368_);
return v___x_1384_;
}
v___jp_1385_:
{
size_t v_sz_1392_; size_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_sz_1392_ = lean_array_size(v___y_1387_);
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1(v_sz_1392_, v___x_1393_, v___y_1387_);
v___x_1395_ = lean_array_get_size(v___x_1394_);
v___x_1396_ = lean_nat_dec_lt(v___y_1388_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___y_1365_ = v___y_1386_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v___y_1390_;
v___y_1368_ = v___y_1391_;
v___y_1369_ = v___x_1394_;
v___y_1370_ = v___x_1397_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___y_1365_ = v___y_1386_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v___y_1390_;
v___y_1368_ = v___y_1391_;
v___y_1369_ = v___x_1394_;
v___y_1370_ = v___x_1398_;
goto v___jp_1364_;
}
}
v___jp_1399_:
{
lean_object* v___x_1405_; lean_object* v_env_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1405_ = lean_st_ref_get(v___y_1404_);
v_env_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_env_1406_);
lean_dec(v___x_1405_);
lean_inc(v_decl_1299_);
v___x_1407_ = l_Lean_Parser_getSyntaxNodeKindCategories(v_env_1406_, v_decl_1299_);
v___x_1408_ = lean_array_get_size(v___x_1407_);
v___x_1409_ = lean_nat_dec_eq(v___x_1408_, v___x_1294_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_lt(v___x_1294_, v___x_1408_);
if (v___x_1410_ == 0)
{
lean_dec(v___x_1293_);
v___y_1386_ = v___y_1403_;
v___y_1387_ = v___x_1407_;
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___y_1404_;
goto v___jp_1385_;
}
else
{
if (v___x_1410_ == 0)
{
lean_dec(v___x_1293_);
v___y_1386_ = v___y_1403_;
v___y_1387_ = v___x_1407_;
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___y_1404_;
goto v___jp_1385_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1408_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(v___y_1401_, v___x_1407_, v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v___x_1293_);
v___y_1386_ = v___y_1403_;
v___y_1387_ = v___x_1407_;
v___y_1388_ = v___y_1400_;
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v___y_1404_;
goto v___jp_1385_;
}
else
{
lean_dec_ref(v___x_1407_);
v___y_1347_ = v___y_1401_;
v___y_1348_ = v___y_1402_;
v___y_1349_ = v___y_1403_;
v___y_1350_ = v___y_1404_;
goto v___jp_1346_;
}
}
}
}
else
{
lean_dec_ref(v___x_1407_);
v___y_1347_ = v___y_1401_;
v___y_1348_ = v___y_1402_;
v___y_1349_ = v___y_1403_;
v___y_1350_ = v___y_1404_;
goto v___jp_1346_;
}
}
v___jp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1418_ = l_Lean_Name_mkStr4(v___x_1295_, v___x_1296_, v___x_1417_, v___x_1297_);
lean_inc(v_stx_1300_);
v___x_1419_ = l_Lean_Syntax_isOfKind(v_stx_1300_, v___x_1418_);
lean_dec(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_stx_1300_);
lean_dec(v_decl_1299_);
lean_dec(v___x_1293_);
v___x_1420_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1421_ = l_Lean_MessageData_ofName(v_name_1298_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1424_, v___y_1415_, v___y_1416_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec(v_name_1298_);
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = l_Lean_Syntax_getArg(v_stx_1300_, v___x_1426_);
lean_dec(v_stx_1300_);
v___x_1428_ = lean_box(0);
lean_inc(v___x_1427_);
v___x_1429_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1427_, v___x_1428_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc_n(v_a_1430_, 2);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = 0;
v___x_1432_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(v_a_1430_, v___x_1431_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; lean_object* v_env_1434_; uint8_t v___x_1435_; 
lean_dec_ref_known(v___x_1432_, 1);
v___x_1433_ = lean_st_ref_get(v___y_1416_);
v_env_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc_ref(v_env_1434_);
lean_dec(v___x_1433_);
v___x_1435_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1434_, v_a_1430_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v_decl_1299_);
lean_dec(v___x_1293_);
v___x_1436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1437_ = l_Lean_MessageData_ofName(v_a_1430_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v___x_1427_, v___x_1440_, v___y_1415_, v___y_1416_);
lean_dec(v___x_1427_);
return v___x_1441_;
}
else
{
lean_dec(v___x_1427_);
v___y_1400_ = v___x_1426_;
v___y_1401_ = v___x_1419_;
v___y_1402_ = v_a_1430_;
v___y_1403_ = v___y_1415_;
v___y_1404_ = v___y_1416_;
goto v___jp_1399_;
}
}
else
{
lean_dec(v_a_1430_);
lean_dec(v___x_1427_);
lean_dec(v_decl_1299_);
lean_dec(v___x_1293_);
return v___x_1432_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v___x_1427_);
lean_dec(v_decl_1299_);
lean_dec(v___x_1293_);
v_a_1442_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1429_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1429_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
v___jp_1450_:
{
lean_object* v___x_1451_; lean_object* v_env_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_st_ref_get(v___y_1303_);
v_env_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc_ref(v_env_1452_);
lean_dec(v___x_1451_);
v___x_1453_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1452_, v_decl_1299_);
lean_dec_ref(v_env_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
v___y_1415_ = v___y_1302_;
v___y_1416_ = v___y_1303_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1454_; 
lean_dec_ref_known(v___x_1453_, 1);
lean_dec(v_stx_1300_);
lean_dec_ref(v___x_1297_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v___x_1295_);
lean_dec(v___x_1293_);
v___x_1454_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_name_1298_, v_decl_1299_, v___y_1302_, v___y_1303_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v___x_1461_, lean_object* v___x_1462_, lean_object* v_name_1463_, lean_object* v_decl_1464_, lean_object* v_stx_1465_, lean_object* v_kind_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_kind_boxed_1470_; lean_object* v_res_1471_; 
v_kind_boxed_1470_ = lean_unbox(v_kind_1466_);
v_res_1471_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(v___x_1458_, v___x_1459_, v___x_1460_, v___x_1461_, v___x_1462_, v_name_1463_, v_decl_1464_, v_stx_1465_, v_kind_boxed_1470_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___x_1459_);
return v_res_1471_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_unsigned_to_nat(2574034933u);
v___x_1536_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1537_ = l_Lean_Name_num___override(v___x_1536_, v___x_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1540_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1541_ = l_Lean_Name_str___override(v___x_1540_, v___x_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1544_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1545_ = l_Lean_Name_str___override(v___x_1544_, v___x_1543_);
return v___x_1545_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1548_ = l_Lean_Name_num___override(v___x_1547_, v___x_1546_);
return v___x_1548_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v_name_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1550_ = 1;
v___x_1551_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v_name_1552_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1553_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v_name_1552_);
lean_ctor_set(v___x_1554_, 2, v___x_1551_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*3, v___x_1550_);
return v___x_1554_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___f_1555_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___f_1556_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1557_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___f_1556_);
lean_ctor_set(v___x_1558_, 2, v___f_1555_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1561_ = l_Lean_registerBuiltinAttribute(v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_();
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1564_, lean_object* v_msg_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v_msg_1565_, v___y_1566_, v___y_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_msg_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0(v_00_u03b1_1570_, v_msg_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1576_, lean_object* v_ref_1577_, lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_ref_1577_, v_msg_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_ref_1584_, lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4(v_00_u03b1_1583_, v_ref_1584_, v_msg_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_ref_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1590_, lean_object* v_attrName_1591_, lean_object* v_declName_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_attrName_1591_, v_declName_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_attrName_1598_, lean_object* v_declName_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5(v_00_u03b1_1597_, v_attrName_1598_, v_declName_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1604_, lean_object* v_name_1605_, uint8_t v_kind_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_1605_, v_kind_1606_, v___y_1607_, v___y_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1611_, lean_object* v_name_1612_, lean_object* v_kind_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v_kind_boxed_1617_; lean_object* v_res_1618_; 
v_kind_boxed_1617_ = lean_unbox(v_kind_1613_);
v_res_1618_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6(v_00_u03b1_1611_, v_name_1612_, v_kind_boxed_1617_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1619_, lean_object* v_m_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v_m_1620_, v_a_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1623_, lean_object* v_m_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1623_, v_m_1624_, v_a_1625_);
lean_dec(v_a_1625_);
lean_dec_ref(v_m_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_x_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b2_1631_, v_x_1632_, v_x_1633_);
lean_dec_ref(v_x_1633_);
lean_dec_ref(v_x_1632_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1636_, lean_object* v_a_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_1637_, v_x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1640_, lean_object* v_a_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9(v_00_u03b2_1640_, v_a_1641_, v_x_1642_);
lean_dec(v_x_1642_);
lean_dec(v_a_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, size_t v_x_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1645_, v_x_1646_, v_x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
size_t v_x_10110__boxed_1653_; uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_x_10110__boxed_1653_ = lean_unbox_usize(v_x_1651_);
lean_dec(v_x_1651_);
v_res_1654_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_00_u03b2_1649_, v_x_1650_, v_x_10110__boxed_1653_, v_x_1652_);
lean_dec_ref(v_x_1652_);
lean_dec_ref(v_x_1650_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1656_, lean_object* v_keys_1657_, lean_object* v_vals_1658_, lean_object* v_heq_1659_, lean_object* v_i_1660_, lean_object* v_k_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_keys_1657_, v_i_1660_, v_k_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b2_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_heq_1666_, lean_object* v_i_1667_, lean_object* v_k_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12(v_00_u03b2_1663_, v_keys_1664_, v_vals_1665_, v_heq_1666_, v_i_1667_, v_k_1668_);
lean_dec_ref(v_k_1668_);
lean_dec_ref(v_vals_1665_);
lean_dec_ref(v_keys_1664_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_fst_1673_; lean_object* v_snd_1674_; lean_object* v___x_1675_; 
v_fst_1673_ = lean_ctor_get(v_x_1672_, 0);
lean_inc(v_fst_1673_);
v_snd_1674_ = lean_ctor_get(v_x_1672_, 1);
lean_inc(v_snd_1674_);
lean_dec_ref(v_x_1672_);
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1673_, v_snd_1674_, v_as_1671_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v_k_1678_; lean_object* v_v_1679_; lean_object* v_l_1680_; lean_object* v_r_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_k_1678_ = lean_ctor_get(v_x_1677_, 1);
v_v_1679_ = lean_ctor_get(v_x_1677_, 2);
v_l_1680_ = lean_ctor_get(v_x_1677_, 3);
v_r_1681_ = lean_ctor_get(v_x_1677_, 4);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1676_, v_l_1680_);
lean_inc(v_v_1679_);
lean_inc(v_k_1678_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_k_1678_);
lean_ctor_set(v___x_1683_, 1, v_v_1679_);
v___x_1684_ = lean_array_push(v___x_1682_, v___x_1683_);
v_init_1676_ = v___x_1684_;
v_x_1677_ = v_r_1681_;
goto _start;
}
else
{
return v_init_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1686_, v_x_1687_);
lean_dec(v_x_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_1689_, lean_object* v_x2_1690_){
_start:
{
lean_object* v_fst_1691_; lean_object* v_fst_1692_; uint8_t v___x_1693_; 
v_fst_1691_ = lean_ctor_get(v_x1_1689_, 0);
v_fst_1692_ = lean_ctor_get(v_x2_1690_, 0);
v___x_1693_ = l_Lean_Name_quickLt(v_fst_1691_, v_fst_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_1694_, lean_object* v_x2_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_1694_, v_x2_1695_);
lean_dec_ref(v_x2_1695_);
lean_dec_ref(v_x1_1694_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1698_, lean_object* v_pivot_1699_, lean_object* v_as_1700_, lean_object* v_i_1701_, lean_object* v_k_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_nat_dec_lt(v_k_1702_, v_hi_1698_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_k_1702_);
v___x_1704_ = lean_array_fswap(v_as_1700_, v_i_1701_, v_hi_1698_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_i_1701_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v_fst_1707_; lean_object* v_fst_1708_; uint8_t v___x_1709_; 
v___x_1706_ = lean_array_fget_borrowed(v_as_1700_, v_k_1702_);
v_fst_1707_ = lean_ctor_get(v___x_1706_, 0);
v_fst_1708_ = lean_ctor_get(v_pivot_1699_, 0);
v___x_1709_ = l_Lean_Name_quickLt(v_fst_1707_, v_fst_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v_k_1702_, v___x_1710_);
lean_dec(v_k_1702_);
v_k_1702_ = v___x_1711_;
goto _start;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1713_ = lean_array_fswap(v_as_1700_, v_i_1701_, v_k_1702_);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_i_1701_, v___x_1714_);
lean_dec(v_i_1701_);
v___x_1716_ = lean_nat_add(v_k_1702_, v___x_1714_);
lean_dec(v_k_1702_);
v_as_1700_ = v___x_1713_;
v_i_1701_ = v___x_1715_;
v_k_1702_ = v___x_1716_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1718_, lean_object* v_pivot_1719_, lean_object* v_as_1720_, lean_object* v_i_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1718_, v_pivot_1719_, v_as_1720_, v_i_1721_, v_k_1722_);
lean_dec_ref(v_pivot_1719_);
lean_dec(v_hi_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1724_, lean_object* v_as_1725_, lean_object* v_lo_1726_, lean_object* v_hi_1727_){
_start:
{
lean_object* v___y_1729_; uint8_t v___x_1739_; 
v___x_1739_ = lean_nat_dec_lt(v_lo_1726_, v_hi_1727_);
if (v___x_1739_ == 0)
{
lean_dec(v_lo_1726_);
return v_as_1725_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_mid_1742_; lean_object* v___y_1744_; lean_object* v___y_1750_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1740_ = lean_nat_add(v_lo_1726_, v_hi_1727_);
v___x_1741_ = lean_unsigned_to_nat(1u);
v_mid_1742_ = lean_nat_shiftr(v___x_1740_, v___x_1741_);
lean_dec(v___x_1740_);
v___x_1755_ = lean_array_fget_borrowed(v_as_1725_, v_mid_1742_);
v___x_1756_ = lean_array_fget_borrowed(v_as_1725_, v_lo_1726_);
v___x_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
v___y_1750_ = v_as_1725_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_array_fswap(v_as_1725_, v_lo_1726_, v_mid_1742_);
v___y_1750_ = v___x_1758_;
goto v___jp_1749_;
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = lean_array_fget_borrowed(v___y_1744_, v_mid_1742_);
v___x_1746_ = lean_array_fget_borrowed(v___y_1744_, v_hi_1727_);
v___x_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_dec(v_mid_1742_);
v___y_1729_ = v___y_1744_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_array_fswap(v___y_1744_, v_mid_1742_, v_hi_1727_);
lean_dec(v_mid_1742_);
v___y_1729_ = v___x_1748_;
goto v___jp_1728_;
}
}
v___jp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = lean_array_fget_borrowed(v___y_1750_, v_hi_1727_);
v___x_1752_ = lean_array_fget_borrowed(v___y_1750_, v_lo_1726_);
v___x_1753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
v___y_1744_ = v___y_1750_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_array_fswap(v___y_1750_, v_lo_1726_, v_hi_1727_);
v___y_1744_ = v___x_1754_;
goto v___jp_1743_;
}
}
}
v___jp_1728_:
{
lean_object* v_pivot_1730_; lean_object* v___x_1731_; lean_object* v_fst_1732_; lean_object* v_snd_1733_; uint8_t v___x_1734_; 
v_pivot_1730_ = lean_array_fget(v___y_1729_, v_hi_1727_);
lean_inc_n(v_lo_1726_, 2);
v___x_1731_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1727_, v_pivot_1730_, v___y_1729_, v_lo_1726_, v_lo_1726_);
lean_dec(v_pivot_1730_);
v_fst_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_fst_1732_);
v_snd_1733_ = lean_ctor_get(v___x_1731_, 1);
lean_inc(v_snd_1733_);
lean_dec_ref(v___x_1731_);
v___x_1734_ = lean_nat_dec_le(v_hi_1727_, v_fst_1732_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1724_, v_snd_1733_, v_lo_1726_, v_fst_1732_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_fst_1732_, v___x_1736_);
lean_dec(v_fst_1732_);
v_as_1725_ = v___x_1735_;
v_lo_1726_ = v___x_1737_;
goto _start;
}
else
{
lean_dec(v_fst_1732_);
lean_dec(v_lo_1726_);
return v_snd_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1759_, lean_object* v_as_1760_, lean_object* v_lo_1761_, lean_object* v_hi_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1759_, v_as_1760_, v_lo_1761_, v_hi_1762_);
lean_dec(v_hi_1762_);
lean_dec(v_n_1759_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_1766_, lean_object* v_s_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; uint8_t v___x_1777_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1770_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1769_, v_s_1767_);
v___x_1771_ = lean_array_get_size(v___x_1770_);
v___x_1777_ = lean_nat_dec_eq(v___x_1771_, v___x_1768_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___y_1781_; uint8_t v___x_1783_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_sub(v___x_1771_, v___x_1778_);
v___x_1783_ = lean_nat_dec_le(v___x_1768_, v___x_1779_);
if (v___x_1783_ == 0)
{
lean_inc(v___x_1779_);
v___y_1781_ = v___x_1779_;
goto v___jp_1780_;
}
else
{
v___y_1781_ = v___x_1768_;
goto v___jp_1780_;
}
v___jp_1780_:
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_nat_dec_le(v___y_1781_, v___x_1779_);
if (v___x_1782_ == 0)
{
lean_dec(v___x_1779_);
lean_inc(v___y_1781_);
v___y_1773_ = v___y_1781_;
v___y_1774_ = v___y_1781_;
goto v___jp_1772_;
}
else
{
v___y_1773_ = v___y_1781_;
v___y_1774_ = v___x_1779_;
goto v___jp_1772_;
}
}
}
else
{
lean_object* v___x_1784_; 
lean_inc_ref_n(v___x_1770_, 2);
v___x_1784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1770_);
lean_ctor_set(v___x_1784_, 1, v___x_1770_);
lean_ctor_set(v___x_1784_, 2, v___x_1770_);
return v___x_1784_;
}
v___jp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1771_, v___x_1770_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_inc_ref_n(v___x_1775_, 2);
v___x_1776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
lean_ctor_set(v___x_1776_, 2, v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_1785_, lean_object* v_s_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_1785_, v_s_1786_);
lean_dec(v_s_1786_);
lean_dec_ref(v_x_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1791_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1790_, v_es_1788_);
v___x_1792_ = lean_array_get_size(v___x_1791_);
v___x_1793_ = lean_nat_dec_eq(v___x_1792_, v___x_1789_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___y_1797_; uint8_t v___x_1801_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_sub(v___x_1792_, v___x_1794_);
v___x_1801_ = lean_nat_dec_le(v___x_1789_, v___x_1795_);
if (v___x_1801_ == 0)
{
lean_inc(v___x_1795_);
v___y_1797_ = v___x_1795_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v___x_1789_;
goto v___jp_1796_;
}
v___jp_1796_:
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_nat_dec_le(v___y_1797_, v___x_1795_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec(v___x_1795_);
lean_inc(v___y_1797_);
v___x_1799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1792_, v___x_1791_, v___y_1797_, v___y_1797_);
lean_dec(v___y_1797_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1792_, v___x_1791_, v___y_1797_, v___x_1795_);
lean_dec(v___x_1795_);
return v___x_1800_;
}
}
}
else
{
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_1802_);
lean_dec(v_es_1802_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1804_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_1809_, v_x_1810_, v___y_1811_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_x_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1841_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_1844_, lean_object* v_t_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1844_, v_t_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_1847_, lean_object* v_t_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_1847_, v_t_1848_);
lean_dec(v_t_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_1850_, lean_object* v_as_1851_, lean_object* v_lo_1852_, lean_object* v_hi_1853_, lean_object* v_w_1854_, lean_object* v_hlo_1855_, lean_object* v_hhi_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1850_, v_as_1851_, v_lo_1852_, v_hi_1853_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1858_, lean_object* v_as_1859_, lean_object* v_lo_1860_, lean_object* v_hi_1861_, lean_object* v_w_1862_, lean_object* v_hlo_1863_, lean_object* v_hhi_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_1858_, v_as_1859_, v_lo_1860_, v_hi_1861_, v_w_1862_, v_hlo_1863_, v_hhi_1864_);
lean_dec(v_hi_1861_);
lean_dec(v_n_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_1866_, lean_object* v_lo_1867_, lean_object* v_hi_1868_, lean_object* v_hhi_1869_, lean_object* v_pivot_1870_, lean_object* v_as_1871_, lean_object* v_i_1872_, lean_object* v_k_1873_, lean_object* v_ilo_1874_, lean_object* v_ik_1875_, lean_object* v_w_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1868_, v_pivot_1870_, v_as_1871_, v_i_1872_, v_k_1873_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_1878_, lean_object* v_lo_1879_, lean_object* v_hi_1880_, lean_object* v_hhi_1881_, lean_object* v_pivot_1882_, lean_object* v_as_1883_, lean_object* v_i_1884_, lean_object* v_k_1885_, lean_object* v_ilo_1886_, lean_object* v_ik_1887_, lean_object* v_w_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(v_n_1878_, v_lo_1879_, v_hi_1880_, v_hhi_1881_, v_pivot_1882_, v_as_1883_, v_i_1884_, v_k_1885_, v_ilo_1886_, v_ik_1887_, v_w_1888_);
lean_dec_ref(v_pivot_1882_);
lean_dec(v_hi_1880_);
lean_dec(v_lo_1879_);
lean_dec(v_n_1878_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_1894_, lean_object* v___x_1895_, lean_object* v_toPure_1896_, lean_object* v___f_1897_, lean_object* v_env_1898_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1898_, v_tag_1894_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v___x_1903_; lean_object* v_toEnvExtension_1904_; lean_object* v_asyncMode_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec_ref(v___f_1897_);
v___x_1903_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1904_ = lean_ctor_get(v___x_1903_, 0);
v_asyncMode_1905_ = lean_ctor_get(v_toEnvExtension_1904_, 2);
v___x_1906_ = lean_box(0);
v___x_1907_ = 0;
v___x_1908_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1895_, v___x_1903_, v_env_1898_, v_asyncMode_1905_, v___x_1906_, v___x_1907_);
v___x_1909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1908_, v_tag_1894_);
lean_dec(v_tag_1894_);
lean_dec(v___x_1908_);
v___x_1910_ = lean_apply_2(v_toPure_1896_, lean_box(0), v___x_1909_);
return v___x_1910_;
}
else
{
lean_object* v_val_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_val_1911_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1912_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_1913_ = 0;
v___x_1914_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1895_, v___x_1912_, v_env_1898_, v_val_1911_, v___x_1913_);
lean_dec(v_val_1911_);
lean_dec_ref(v_env_1898_);
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v___x_1914_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v___x_1914_);
lean_dec_ref(v___f_1897_);
lean_dec(v_tag_1894_);
goto v___jp_1899_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_sub(v___x_1916_, v___x_1918_);
v___x_1920_ = lean_nat_dec_le(v___x_1915_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_dec(v___x_1919_);
lean_dec_ref(v___x_1914_);
lean_dec_ref(v___f_1897_);
lean_dec(v_tag_1894_);
goto v___jp_1899_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1921_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_tag_1894_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_1924_ = l_Array_binSearchAux___redArg(v___f_1897_, v___x_1923_, v___x_1914_, v___x_1922_, v___x_1915_, v___x_1919_);
lean_dec_ref(v___x_1914_);
if (lean_obj_tag(v___x_1924_) == 0)
{
goto v___jp_1899_;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1934_; 
v_val_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_val_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_snd_1929_; lean_object* v___x_1931_; 
v_snd_1929_ = lean_ctor_get(v_val_1925_, 1);
lean_inc(v_snd_1929_);
lean_dec(v_val_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v_snd_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_snd_1929_);
v___x_1931_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_apply_2(v_toPure_1896_, lean_box(0), v___x_1931_);
return v___x_1932_;
}
}
}
}
}
}
v___jp_1899_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_apply_2(v_toPure_1896_, lean_box(0), v___x_1900_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_tag_1938_){
_start:
{
lean_object* v_toApplicative_1939_; lean_object* v_toBind_1940_; lean_object* v_getEnv_1941_; lean_object* v_toPure_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; 
v_toApplicative_1939_ = lean_ctor_get(v_inst_1936_, 0);
lean_inc_ref(v_toApplicative_1939_);
v_toBind_1940_ = lean_ctor_get(v_inst_1936_, 1);
lean_inc(v_toBind_1940_);
lean_dec_ref(v_inst_1936_);
v_getEnv_1941_ = lean_ctor_get(v_inst_1937_, 0);
lean_inc(v_getEnv_1941_);
lean_dec_ref(v_inst_1937_);
v_toPure_1942_ = lean_ctor_get(v_toApplicative_1939_, 1);
lean_inc(v_toPure_1942_);
lean_dec_ref(v_toApplicative_1939_);
v___f_1943_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0));
v___x_1944_ = lean_box(1);
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1945_, 0, v_tag_1938_);
lean_closure_set(v___f_1945_, 1, v___x_1944_);
lean_closure_set(v___f_1945_, 2, v_toPure_1942_);
lean_closure_set(v___f_1945_, 3, v___f_1943_);
v___x_1946_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v_getEnv_1941_, v___f_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_tag_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_1948_, v_inst_1949_, v_tag_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_1952_, lean_object* v_k_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_array_push(v_l_1952_, v_k_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_1956_, lean_object* v_x2_1957_){
_start:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1958_ = 1;
v___x_1959_ = l_Lean_Name_toString(v_x1_1956_, v___x_1958_);
v___x_1960_ = l_Lean_Name_toString(v_x2_1957_, v___x_1958_);
v___x_1961_ = lean_string_dec_lt(v___x_1959_, v___x_1960_);
lean_dec_ref(v___x_1960_);
lean_dec_ref(v___x_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_1962_, lean_object* v_x2_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_1962_, v_x2_1963_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_1966_, lean_object* v_a_1967_, lean_object* v_b_1968_, lean_object* v_c_1969_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = l_Lean_NameSet_insert(v_c_1969_, v_a_1967_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
v___x_1972_ = lean_apply_2(v_toPure_1966_, lean_box(0), v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_1973_, lean_object* v_a_1974_, lean_object* v_b_1975_, lean_object* v_c_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_1973_, v_a_1974_, v_b_1975_, v_c_1976_);
lean_dec_ref(v_b_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_1978_, lean_object* v_a_1979_, lean_object* v_x_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_fst_1982_; lean_object* v_found_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_fst_1982_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_fst_1982_);
lean_dec_ref(v_a_1979_);
v_found_1983_ = l_Lean_NameSet_insert(v___y_1981_, v_fst_1982_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_found_1983_);
v___x_1985_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_1986_, lean_object* v___f_1987_, lean_object* v_toBind_1988_, lean_object* v___f_1989_, lean_object* v_a_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v_sz_1993_ = lean_array_size(v_a_1990_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1986_, v_a_1990_, v___f_1987_, v_sz_1993_, v___x_1994_, v___y_1992_);
v___x_1996_ = lean_apply_4(v_toBind_1988_, lean_box(0), lean_box(0), v___x_1995_, v___f_1989_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_1997_, lean_object* v___f_1998_, lean_object* v___f_1999_, lean_object* v_____s_2000_){
_start:
{
lean_object* v___y_2002_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2018_; 
if (lean_obj_tag(v_____s_2000_) == 0)
{
lean_object* v_size_2027_; 
v_size_2027_ = lean_ctor_get(v_____s_2000_, 0);
lean_inc(v_size_2027_);
v___y_2018_ = v_size_2027_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___y_2018_ = v___x_2028_;
goto v___jp_2017_;
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_array_to_list(v___y_2002_);
v___x_2004_ = lean_apply_2(v_toPure_1997_, lean_box(0), v___x_2003_);
return v___x_2004_;
}
v___jp_2005_:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1998_, v___y_2007_, v___y_2008_, v___y_2006_, v___y_2009_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2009_);
lean_dec(v___y_2007_);
v___y_2002_ = v___x_2010_;
goto v___jp_2001_;
}
v___jp_2011_:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_nat_dec_le(v___y_2015_, v___y_2014_);
if (v___x_2016_ == 0)
{
lean_dec(v___y_2014_);
lean_inc(v___y_2015_);
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2012_;
v___y_2008_ = v___y_2013_;
v___y_2009_ = v___y_2015_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2012_;
v___y_2008_ = v___y_2013_;
v___y_2009_ = v___y_2014_;
goto v___jp_2005_;
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2019_ = lean_mk_empty_array_with_capacity(v___y_2018_);
lean_dec(v___y_2018_);
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1999_, v___x_2019_, v_____s_2000_);
v___x_2021_ = lean_array_get_size(v___x_2020_);
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = lean_nat_dec_eq(v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_sub(v___x_2021_, v___x_2024_);
v___x_2026_ = lean_nat_dec_le(v___x_2022_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_inc(v___x_2025_);
v___y_2012_ = v___x_2021_;
v___y_2013_ = v___x_2020_;
v___y_2014_ = v___x_2025_;
v___y_2015_ = v___x_2025_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___x_2021_;
v___y_2013_ = v___x_2020_;
v___y_2014_ = v___x_2025_;
v___y_2015_ = v___x_2022_;
goto v___jp_2011_;
}
}
else
{
lean_dec_ref(v___f_1998_);
v___y_2002_ = v___x_2020_;
goto v___jp_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2029_, lean_object* v_toEnvExtension_2030_, lean_object* v_env_2031_, lean_object* v_asyncMode_2032_, lean_object* v___x_2033_, uint8_t v___x_2034_, lean_object* v_inst_2035_, lean_object* v___f_2036_, lean_object* v_toBind_2037_, lean_object* v___f_2038_, lean_object* v_____s_2039_){
_start:
{
lean_object* v___x_2040_; lean_object* v_importedEntries_2041_; size_t v_sz_2042_; size_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2040_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2029_, v_toEnvExtension_2030_, v_env_2031_, v_asyncMode_2032_, v___x_2033_, v___x_2034_);
v_importedEntries_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc_ref(v_importedEntries_2041_);
lean_dec(v___x_2040_);
v_sz_2042_ = lean_array_size(v_importedEntries_2041_);
v___x_2043_ = ((size_t)0ULL);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2035_, v_importedEntries_2041_, v___f_2036_, v_sz_2042_, v___x_2043_, v_____s_2039_);
v___x_2045_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v___x_2044_, v___f_2038_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2046_, lean_object* v_toEnvExtension_2047_, lean_object* v_env_2048_, lean_object* v_asyncMode_2049_, lean_object* v___x_2050_, lean_object* v___x_2051_, lean_object* v_inst_2052_, lean_object* v___f_2053_, lean_object* v_toBind_2054_, lean_object* v___f_2055_, lean_object* v_____s_2056_){
_start:
{
uint8_t v___x_532__boxed_2057_; lean_object* v_res_2058_; 
v___x_532__boxed_2057_ = lean_unbox(v___x_2051_);
v_res_2058_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2046_, v_toEnvExtension_2047_, v_env_2048_, v_asyncMode_2049_, v___x_2050_, v___x_532__boxed_2057_, v_inst_2052_, v___f_2053_, v_toBind_2054_, v___f_2055_, v_____s_2056_);
lean_dec(v_asyncMode_2049_);
lean_dec_ref(v_toEnvExtension_2047_);
lean_dec_ref(v___x_2046_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2059_, lean_object* v_inst_2060_, lean_object* v___f_2061_, lean_object* v_toBind_2062_, lean_object* v___f_2063_, lean_object* v___x_2064_, lean_object* v___f_2065_, lean_object* v___f_2066_, lean_object* v_env_2067_){
_start:
{
lean_object* v___x_2068_; lean_object* v_toEnvExtension_2069_; lean_object* v_asyncMode_2070_; lean_object* v_found_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2068_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2069_ = lean_ctor_get(v___x_2068_, 0);
v_asyncMode_2070_ = lean_ctor_get(v_toEnvExtension_2069_, 2);
v_found_2071_ = l_Lean_NameSet_empty;
v___x_2072_ = lean_box(0);
v___x_2073_ = 0;
v___x_2074_ = lean_box(v___x_2073_);
lean_inc_n(v_toBind_2062_, 2);
lean_inc_ref(v_inst_2060_);
lean_inc(v_asyncMode_2070_);
lean_inc_ref(v_env_2067_);
lean_inc_ref(v_toEnvExtension_2069_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_2075_, 0, v___x_2059_);
lean_closure_set(v___f_2075_, 1, v_toEnvExtension_2069_);
lean_closure_set(v___f_2075_, 2, v_env_2067_);
lean_closure_set(v___f_2075_, 3, v_asyncMode_2070_);
lean_closure_set(v___f_2075_, 4, v___x_2072_);
lean_closure_set(v___f_2075_, 5, v___x_2074_);
lean_closure_set(v___f_2075_, 6, v_inst_2060_);
lean_closure_set(v___f_2075_, 7, v___f_2061_);
lean_closure_set(v___f_2075_, 8, v_toBind_2062_);
lean_closure_set(v___f_2075_, 9, v___f_2063_);
v___x_2076_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2064_, v___x_2068_, v_env_2067_, v_asyncMode_2070_, v___x_2072_, v___x_2073_);
v___x_2077_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2060_, v___f_2065_, v_found_2071_, v___x_2076_);
v___x_2078_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2077_, v___f_2066_);
v___x_2079_ = lean_apply_4(v_toBind_2062_, lean_box(0), lean_box(0), v___x_2078_, v___f_2075_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2082_, lean_object* v_inst_2083_){
_start:
{
lean_object* v_toApplicative_2084_; lean_object* v_toBind_2085_; lean_object* v_getEnv_2086_; lean_object* v_toPure_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; 
v_toApplicative_2084_ = lean_ctor_get(v_inst_2082_, 0);
v_toBind_2085_ = lean_ctor_get(v_inst_2082_, 1);
lean_inc_n(v_toBind_2085_, 3);
v_getEnv_2086_ = lean_ctor_get(v_inst_2083_, 0);
lean_inc(v_getEnv_2086_);
lean_dec_ref(v_inst_2083_);
v_toPure_2087_ = lean_ctor_get(v_toApplicative_2084_, 1);
v___f_2088_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2089_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2090_ = lean_box(1);
v___x_2091_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_2087_, 5);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2092_, 0, v_toPure_2087_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2093_, 0, v_toPure_2087_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2094_, 0, v_toPure_2087_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2095_, 0, v_toPure_2087_);
lean_inc_ref(v_inst_2082_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2096_, 0, v_inst_2082_);
lean_closure_set(v___f_2096_, 1, v___f_2094_);
lean_closure_set(v___f_2096_, 2, v_toBind_2085_);
lean_closure_set(v___f_2096_, 3, v___f_2095_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2097_, 0, v_toPure_2087_);
lean_closure_set(v___f_2097_, 1, v___f_2089_);
lean_closure_set(v___f_2097_, 2, v___f_2088_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2098_, 0, v___x_2091_);
lean_closure_set(v___f_2098_, 1, v_inst_2082_);
lean_closure_set(v___f_2098_, 2, v___f_2096_);
lean_closure_set(v___f_2098_, 3, v_toBind_2085_);
lean_closure_set(v___f_2098_, 4, v___f_2097_);
lean_closure_set(v___f_2098_, 5, v___x_2090_);
lean_closure_set(v___f_2098_, 6, v___f_2093_);
lean_closure_set(v___f_2098_, 7, v___f_2092_);
v___x_2099_ = lean_apply_4(v_toBind_2085_, lean_box(0), lean_box(0), v_getEnv_2086_, v___f_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2101_, v_inst_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2104_, lean_object* v_k_2105_, lean_object* v_v_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_k_2105_);
lean_ctor_set(v___x_2107_, 1, v_v_2106_);
v___x_2108_ = lean_array_push(v_arr_2104_, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2109_, lean_object* v_x2_2110_){
_start:
{
lean_object* v_fst_2111_; lean_object* v_fst_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_fst_2111_ = lean_ctor_get(v_x1_2109_, 0);
lean_inc(v_fst_2111_);
lean_dec_ref(v_x1_2109_);
v_fst_2112_ = lean_ctor_get(v_x2_2110_, 0);
lean_inc(v_fst_2112_);
lean_dec_ref(v_x2_2110_);
v___x_2113_ = 1;
v___x_2114_ = l_Lean_Name_toString(v_fst_2111_, v___x_2113_);
v___x_2115_ = l_Lean_Name_toString(v_fst_2112_, v___x_2113_);
v___x_2116_ = lean_string_dec_lt(v___x_2114_, v___x_2115_);
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2117_, lean_object* v_x2_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2117_, v_x2_2118_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2121_, lean_object* v_a_2122_, lean_object* v_b_2123_, lean_object* v_c_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2122_, v_b_2123_, v_c_2124_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = lean_apply_2(v_toPure_2121_, lean_box(0), v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2128_, lean_object* v_a_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_fst_2132_; lean_object* v_snd_2133_; lean_object* v_found_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_fst_2132_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_fst_2132_);
v_snd_2133_ = lean_ctor_get(v_a_2129_, 1);
lean_inc(v_snd_2133_);
lean_dec_ref(v_a_2129_);
v_found_2134_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2132_, v_snd_2133_, v___y_2131_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_found_2134_);
v___x_2136_ = lean_apply_2(v_toPure_2128_, lean_box(0), v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2137_, lean_object* v___f_2138_, lean_object* v___f_2139_, lean_object* v_____s_2140_){
_start:
{
lean_object* v___y_2142_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_arr_2147_; lean_object* v___x_2148_; lean_object* v___y_2150_; lean_object* v___y_2151_; uint8_t v___x_2153_; 
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2147_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2138_, v___x_2146_, v_____s_2140_);
v___x_2148_ = lean_array_get_size(v_arr_2147_);
v___x_2153_ = lean_nat_dec_eq(v___x_2148_, v___x_2145_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___y_2157_; uint8_t v___x_2159_; 
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = lean_nat_sub(v___x_2148_, v___x_2154_);
v___x_2159_ = lean_nat_dec_le(v___x_2145_, v___x_2155_);
if (v___x_2159_ == 0)
{
lean_inc(v___x_2155_);
v___y_2157_ = v___x_2155_;
goto v___jp_2156_;
}
else
{
v___y_2157_ = v___x_2145_;
goto v___jp_2156_;
}
v___jp_2156_:
{
uint8_t v___x_2158_; 
v___x_2158_ = lean_nat_dec_le(v___y_2157_, v___x_2155_);
if (v___x_2158_ == 0)
{
lean_dec(v___x_2155_);
lean_inc(v___y_2157_);
v___y_2150_ = v___y_2157_;
v___y_2151_ = v___y_2157_;
goto v___jp_2149_;
}
else
{
v___y_2150_ = v___y_2157_;
v___y_2151_ = v___x_2155_;
goto v___jp_2149_;
}
}
}
else
{
lean_dec_ref(v___f_2139_);
v___y_2142_ = v_arr_2147_;
goto v___jp_2141_;
}
v___jp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_array_to_list(v___y_2142_);
v___x_2144_ = lean_apply_2(v_toPure_2137_, lean_box(0), v___x_2143_);
return v___x_2144_;
}
v___jp_2149_:
{
lean_object* v___x_2152_; 
v___x_2152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2139_, v___x_2148_, v_arr_2147_, v___y_2150_, v___y_2151_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2151_);
v___y_2142_ = v___x_2152_;
goto v___jp_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2160_, lean_object* v_inst_2161_, lean_object* v___f_2162_, lean_object* v_toBind_2163_, lean_object* v___f_2164_, lean_object* v___x_2165_, lean_object* v___f_2166_, lean_object* v___f_2167_, lean_object* v_env_2168_){
_start:
{
lean_object* v___x_2169_; lean_object* v_toEnvExtension_2170_; lean_object* v_asyncMode_2171_; lean_object* v_found_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2169_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2170_ = lean_ctor_get(v___x_2169_, 0);
v_asyncMode_2171_ = lean_ctor_get(v_toEnvExtension_2170_, 2);
v_found_2172_ = lean_box(1);
v___x_2173_ = lean_box(0);
v___x_2174_ = 0;
v___x_2175_ = lean_box(v___x_2174_);
lean_inc_n(v_toBind_2163_, 2);
lean_inc_ref(v_inst_2161_);
lean_inc(v_asyncMode_2171_);
lean_inc_ref(v_env_2168_);
lean_inc_ref(v_toEnvExtension_2170_);
v___f_2176_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_2176_, 0, v___x_2160_);
lean_closure_set(v___f_2176_, 1, v_toEnvExtension_2170_);
lean_closure_set(v___f_2176_, 2, v_env_2168_);
lean_closure_set(v___f_2176_, 3, v_asyncMode_2171_);
lean_closure_set(v___f_2176_, 4, v___x_2173_);
lean_closure_set(v___f_2176_, 5, v___x_2175_);
lean_closure_set(v___f_2176_, 6, v_inst_2161_);
lean_closure_set(v___f_2176_, 7, v___f_2162_);
lean_closure_set(v___f_2176_, 8, v_toBind_2163_);
lean_closure_set(v___f_2176_, 9, v___f_2164_);
v___x_2177_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2165_, v___x_2169_, v_env_2168_, v_asyncMode_2171_, v___x_2173_, v___x_2174_);
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2161_, v___f_2166_, v_found_2172_, v___x_2177_);
v___x_2179_ = lean_apply_4(v_toBind_2163_, lean_box(0), lean_box(0), v___x_2178_, v___f_2167_);
v___x_2180_ = lean_apply_4(v_toBind_2163_, lean_box(0), lean_box(0), v___x_2179_, v___f_2176_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v_toApplicative_2185_; lean_object* v_toBind_2186_; lean_object* v_getEnv_2187_; lean_object* v_toPure_2188_; lean_object* v___f_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
v_toApplicative_2185_ = lean_ctor_get(v_inst_2183_, 0);
v_toBind_2186_ = lean_ctor_get(v_inst_2183_, 1);
lean_inc_n(v_toBind_2186_, 3);
v_getEnv_2187_ = lean_ctor_get(v_inst_2184_, 0);
lean_inc(v_getEnv_2187_);
lean_dec_ref(v_inst_2184_);
v_toPure_2188_ = lean_ctor_get(v_toApplicative_2185_, 1);
v___f_2189_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2190_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2191_ = lean_box(1);
v___x_2192_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_2188_, 5);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2188_);
v___f_2194_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2194_, 0, v_toPure_2188_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2195_, 0, v_toPure_2188_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2196_, 0, v_toPure_2188_);
lean_inc_ref(v_inst_2183_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2197_, 0, v_inst_2183_);
lean_closure_set(v___f_2197_, 1, v___f_2195_);
lean_closure_set(v___f_2197_, 2, v_toBind_2186_);
lean_closure_set(v___f_2197_, 3, v___f_2196_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2198_, 0, v_toPure_2188_);
lean_closure_set(v___f_2198_, 1, v___f_2189_);
lean_closure_set(v___f_2198_, 2, v___f_2190_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2199_, 0, v___x_2192_);
lean_closure_set(v___f_2199_, 1, v_inst_2183_);
lean_closure_set(v___f_2199_, 2, v___f_2197_);
lean_closure_set(v___f_2199_, 3, v_toBind_2186_);
lean_closure_set(v___f_2199_, 4, v___f_2198_);
lean_closure_set(v___f_2199_, 5, v___x_2191_);
lean_closure_set(v___f_2199_, 6, v___f_2194_);
lean_closure_set(v___f_2199_, 7, v___f_2193_);
v___x_2200_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v_getEnv_2187_, v___f_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2202_, v_inst_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2205_, lean_object* v_init_2206_, lean_object* v_x_2207_){
_start:
{
if (lean_obj_tag(v_x_2207_) == 0)
{
lean_object* v_k_2208_; lean_object* v_l_2209_; lean_object* v_r_2210_; lean_object* v___x_2211_; lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_k_2208_ = lean_ctor_get(v_x_2207_, 1);
v_l_2209_ = lean_ctor_get(v_x_2207_, 3);
v_r_2210_ = lean_ctor_get(v_x_2207_, 4);
lean_inc_n(v_a_2205_, 2);
v___x_2211_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2205_, v_init_2206_, v_l_2209_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
lean_inc(v_k_2208_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_a_2205_);
lean_ctor_set(v___x_2213_, 1, v_k_2208_);
v___x_2214_ = lean_array_push(v_a_2212_, v___x_2213_);
v_init_2206_ = v___x_2214_;
v_x_2207_ = v_r_2210_;
goto _start;
}
else
{
lean_object* v___x_2216_; 
lean_dec(v_a_2205_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_init_2206_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2217_, lean_object* v_init_2218_, lean_object* v_x_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2217_, v_init_2218_, v_x_2219_);
lean_dec(v_x_2219_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2221_, lean_object* v_x_2222_){
_start:
{
if (lean_obj_tag(v_x_2222_) == 0)
{
lean_object* v_k_2223_; lean_object* v_v_2224_; lean_object* v_l_2225_; lean_object* v_r_2226_; lean_object* v___x_2227_; lean_object* v_a_2228_; lean_object* v___x_2229_; lean_object* v_a_2230_; 
v_k_2223_ = lean_ctor_get(v_x_2222_, 1);
lean_inc(v_k_2223_);
v_v_2224_ = lean_ctor_get(v_x_2222_, 2);
lean_inc(v_v_2224_);
v_l_2225_ = lean_ctor_get(v_x_2222_, 3);
lean_inc(v_l_2225_);
v_r_2226_ = lean_ctor_get(v_x_2222_, 4);
lean_inc(v_r_2226_);
lean_dec_ref_known(v_x_2222_, 5);
v___x_2227_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2221_, v_l_2225_);
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2223_, v_a_2228_, v_v_2224_);
lean_dec(v_v_2224_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v_init_2221_ = v_a_2230_;
v_x_2222_ = v_r_2226_;
goto _start;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v_init_2221_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2233_){
_start:
{
lean_object* v_exported_2234_; lean_object* v___x_2235_; lean_object* v_a_2236_; 
v_exported_2234_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2235_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2234_, v_tags_2233_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
return v_a_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2237_, lean_object* v_s_2238_){
_start:
{
lean_object* v_exported_2239_; lean_object* v___x_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_exported_2239_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2240_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2239_, v_s_2238_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_n(v_a_2241_, 3);
lean_dec_ref(v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2241_);
lean_ctor_set(v___x_2242_, 1, v_a_2241_);
lean_ctor_set(v___x_2242_, 2, v_a_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2243_, lean_object* v_s_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2243_, v_s_2244_);
lean_dec_ref(v_x_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2246_, lean_object* v_k_2247_, lean_object* v_fallback_2248_){
_start:
{
if (lean_obj_tag(v_t_2246_) == 0)
{
lean_object* v_k_2249_; lean_object* v_v_2250_; lean_object* v_l_2251_; lean_object* v_r_2252_; uint8_t v___x_2253_; 
v_k_2249_ = lean_ctor_get(v_t_2246_, 1);
v_v_2250_ = lean_ctor_get(v_t_2246_, 2);
v_l_2251_ = lean_ctor_get(v_t_2246_, 3);
v_r_2252_ = lean_ctor_get(v_t_2246_, 4);
v___x_2253_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2247_, v_k_2249_);
switch(v___x_2253_)
{
case 0:
{
v_t_2246_ = v_l_2251_;
goto _start;
}
case 1:
{
lean_inc(v_v_2250_);
return v_v_2250_;
}
default: 
{
v_t_2246_ = v_r_2252_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2248_);
return v_fallback_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2256_, lean_object* v_k_2257_, lean_object* v_fallback_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2256_, v_k_2257_, v_fallback_2258_);
lean_dec(v_fallback_2258_);
lean_dec(v_k_2257_);
lean_dec(v_t_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v_fst_2262_; lean_object* v_snd_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_fst_2262_ = lean_ctor_get(v_x_2261_, 0);
lean_inc(v_fst_2262_);
v_snd_2263_ = lean_ctor_get(v_x_2261_, 1);
lean_inc(v_snd_2263_);
lean_dec_ref(v_x_2261_);
v___x_2264_ = l_Lean_NameSet_empty;
v___x_2265_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2260_, v_fst_2262_, v___x_2264_);
v___x_2266_ = l_Lean_NameSet_insert(v___x_2265_, v_snd_2263_);
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2262_, v___x_2266_, v_tags_2260_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2293_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2296_, lean_object* v_t_2297_, lean_object* v_k_2298_, lean_object* v_fallback_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2297_, v_k_2298_, v_fallback_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2301_, lean_object* v_t_2302_, lean_object* v_k_2303_, lean_object* v_fallback_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2301_, v_t_2302_, v_k_2303_, v_fallback_2304_);
lean_dec(v_fallback_2304_);
lean_dec(v_k_2303_);
lean_dec(v_t_2302_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
if (lean_obj_tag(v_a_2306_) == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = l_List_reverse___redArg(v_a_2307_);
return v___x_2308_;
}
else
{
lean_object* v_head_2309_; lean_object* v_tail_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2322_; 
v_head_2309_ = lean_ctor_get(v_a_2306_, 0);
v_tail_2310_ = lean_ctor_get(v_a_2306_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2306_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2312_ = v_a_2306_;
v_isShared_2313_ = v_isSharedCheck_2322_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_tail_2310_);
lean_inc(v_head_2309_);
lean_dec(v_a_2306_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2322_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2314_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2315_ = l_Lean_MessageData_ofName(v_head_2309_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v___x_2314_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 1, v_a_2307_);
lean_ctor_set(v___x_2312_, 0, v___x_2317_);
v___x_2319_ = v___x_2312_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_a_2307_);
v___x_2319_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
v_a_2306_ = v_tail_2310_;
v_a_2307_ = v___x_2319_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___lam__0(lean_object* v_addEntryFn_2323_, lean_object* v___x_2324_, lean_object* v_s_2325_){
_start:
{
lean_object* v_importedEntries_2326_; lean_object* v_state_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2335_; 
v_importedEntries_2326_ = lean_ctor_get(v_s_2325_, 0);
v_state_2327_ = lean_ctor_get(v_s_2325_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_s_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2329_ = v_s_2325_;
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_state_2327_);
lean_inc(v_importedEntries_2326_);
lean_dec(v_s_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_state_2331_; lean_object* v___x_2333_; 
v_state_2331_ = lean_apply_2(v_addEntryFn_2323_, v_state_2327_, v___x_2324_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v_state_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_importedEntries_2326_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_state_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2336_, lean_object* v_k_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v_m_2342_; lean_object* v_a_2343_; uint8_t v___x_2344_; 
v___x_2340_ = lean_nat_add(v_x_2338_, v_x_2339_);
v___x_2341_ = lean_unsigned_to_nat(1u);
v_m_2342_ = lean_nat_shiftr(v___x_2340_, v___x_2341_);
lean_dec(v___x_2340_);
v_a_2343_ = lean_array_fget_borrowed(v_as_2336_, v_m_2342_);
v___x_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2343_, v_k_2337_);
if (v___x_2344_ == 0)
{
uint8_t v___x_2345_; 
lean_dec(v_x_2339_);
v___x_2345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2337_, v_a_2343_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; 
lean_dec(v_m_2342_);
lean_dec(v_x_2338_);
lean_inc(v_a_2343_);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_a_2343_);
return v___x_2346_;
}
else
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_nat_dec_eq(v_m_2342_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2349_ = lean_nat_sub(v_m_2342_, v___x_2341_);
lean_dec(v_m_2342_);
v___x_2350_ = lean_nat_dec_lt(v___x_2349_, v_x_2338_);
if (v___x_2350_ == 0)
{
v_x_2339_ = v___x_2349_;
goto _start;
}
else
{
lean_object* v___x_2352_; 
lean_dec(v___x_2349_);
lean_dec(v_x_2338_);
v___x_2352_ = lean_box(0);
return v___x_2352_;
}
}
else
{
lean_object* v___x_2353_; 
lean_dec(v_m_2342_);
lean_dec(v_x_2338_);
v___x_2353_ = lean_box(0);
return v___x_2353_;
}
}
}
else
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
lean_dec(v_x_2338_);
v___x_2354_ = lean_nat_add(v_m_2342_, v___x_2341_);
lean_dec(v_m_2342_);
v___x_2355_ = lean_nat_dec_le(v___x_2354_, v_x_2339_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec(v___x_2354_);
lean_dec(v_x_2339_);
v___x_2356_ = lean_box(0);
return v___x_2356_;
}
else
{
v_x_2338_ = v___x_2354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2358_, lean_object* v_k_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2358_, v_k_2359_, v_x_2360_, v_x_2361_);
lean_dec_ref(v_k_2359_);
lean_dec_ref(v_as_2358_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_env_2371_; lean_object* v___x_2372_; 
v___x_2366_ = lean_box(1);
v___x_2367_ = lean_st_ref_get(v___y_2364_);
v_env_2371_ = lean_ctor_get(v___x_2367_, 0);
lean_inc_ref(v_env_2371_);
lean_dec(v___x_2367_);
v___x_2372_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2371_, v_tag_2363_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; lean_object* v_toEnvExtension_2374_; lean_object* v_asyncMode_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2373_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2374_ = lean_ctor_get(v___x_2373_, 0);
v_asyncMode_2375_ = lean_ctor_get(v_toEnvExtension_2374_, 2);
v___x_2376_ = lean_box(0);
v___x_2377_ = 0;
v___x_2378_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2366_, v___x_2373_, v_env_2371_, v_asyncMode_2375_, v___x_2376_, v___x_2377_);
v___x_2379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2378_, v_tag_2363_);
lean_dec(v_tag_2363_);
lean_dec(v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
else
{
lean_object* v_val_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2409_; 
v_val_2381_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2383_ = v___x_2372_;
v_isShared_2384_ = v_isSharedCheck_2409_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_val_2381_);
lean_dec(v___x_2372_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2409_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2385_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2386_ = 0;
v___x_2387_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2366_, v___x_2385_, v_env_2371_, v_val_2381_, v___x_2386_);
lean_dec(v_val_2381_);
lean_dec_ref(v_env_2371_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = lean_array_get_size(v___x_2387_);
v___x_2390_ = lean_nat_dec_lt(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_dec_ref(v___x_2387_);
lean_del_object(v___x_2383_);
lean_dec(v_tag_2363_);
goto v___jp_2368_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_nat_sub(v___x_2389_, v___x_2391_);
v___x_2393_ = lean_nat_dec_le(v___x_2388_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_dec(v___x_2392_);
lean_dec_ref(v___x_2387_);
lean_del_object(v___x_2383_);
lean_dec(v_tag_2363_);
goto v___jp_2368_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_tag_2363_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2387_, v___x_2395_, v___x_2388_, v___x_2392_);
lean_dec_ref_known(v___x_2395_, 2);
lean_dec_ref(v___x_2387_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_del_object(v___x_2383_);
goto v___jp_2368_;
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2408_; 
v_val_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2408_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_val_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2408_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_snd_2401_; lean_object* v___x_2403_; 
v_snd_2401_ = lean_ctor_get(v_val_2397_, 1);
lean_inc(v_snd_2401_);
lean_dec(v_val_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_snd_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_snd_2401_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set_tag(v___x_2383_, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2403_);
v___x_2405_ = v___x_2383_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
}
}
v___jp_2368_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2410_, v___y_2411_);
lean_dec(v___y_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2414_, size_t v_sz_2415_, size_t v_i_2416_, lean_object* v_b_2417_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_usize_dec_lt(v_i_2416_, v_sz_2415_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_b_2417_);
return v___x_2420_;
}
else
{
lean_object* v_a_2421_; lean_object* v_fst_2422_; lean_object* v_found_2423_; size_t v___x_2424_; size_t v___x_2425_; 
v_a_2421_ = lean_array_uget_borrowed(v_as_2414_, v_i_2416_);
v_fst_2422_ = lean_ctor_get(v_a_2421_, 0);
lean_inc(v_fst_2422_);
v_found_2423_ = l_Lean_NameSet_insert(v_b_2417_, v_fst_2422_);
v___x_2424_ = ((size_t)1ULL);
v___x_2425_ = lean_usize_add(v_i_2416_, v___x_2424_);
v_i_2416_ = v___x_2425_;
v_b_2417_ = v_found_2423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2427_, lean_object* v_sz_2428_, lean_object* v_i_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_){
_start:
{
size_t v_sz_boxed_2432_; size_t v_i_boxed_2433_; lean_object* v_res_2434_; 
v_sz_boxed_2432_ = lean_unbox_usize(v_sz_2428_);
lean_dec(v_sz_2428_);
v_i_boxed_2433_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2427_, v_sz_boxed_2432_, v_i_boxed_2433_, v_b_2430_);
lean_dec_ref(v_as_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2435_, size_t v_sz_2436_, size_t v_i_2437_, lean_object* v_b_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_usize_dec_lt(v_i_2437_, v_sz_2436_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v_b_2438_);
return v___x_2443_;
}
else
{
lean_object* v_a_2444_; size_t v_sz_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v_a_2444_ = lean_array_uget_borrowed(v_as_2435_, v_i_2437_);
v_sz_2445_ = lean_array_size(v_a_2444_);
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2444_, v_sz_2445_, v___x_2446_, v_b_2438_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; size_t v___x_2449_; size_t v___x_2450_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2437_, v___x_2449_);
v_i_2437_ = v___x_2450_;
v_b_2438_ = v_a_2448_;
goto _start;
}
else
{
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2452_, lean_object* v_sz_2453_, lean_object* v_i_2454_, lean_object* v_b_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
size_t v_sz_boxed_2459_; size_t v_i_boxed_2460_; lean_object* v_res_2461_; 
v_sz_boxed_2459_ = lean_unbox_usize(v_sz_2453_);
lean_dec(v_sz_2453_);
v_i_boxed_2460_ = lean_unbox_usize(v_i_2454_);
lean_dec(v_i_2454_);
v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2452_, v_sz_boxed_2459_, v_i_boxed_2460_, v_b_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_as_2452_);
return v_res_2461_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2462_, lean_object* v_x1_2463_, lean_object* v_x2_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = l_Lean_Name_toString(v_x1_2463_, v___x_2462_);
v___x_2466_ = l_Lean_Name_toString(v_x2_2464_, v___x_2462_);
v___x_2467_ = lean_string_dec_lt(v___x_2465_, v___x_2466_);
lean_dec_ref(v___x_2466_);
lean_dec_ref(v___x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2468_, lean_object* v_x1_2469_, lean_object* v_x2_2470_){
_start:
{
uint8_t v___x_6897__boxed_2471_; uint8_t v_res_2472_; lean_object* v_r_2473_; 
v___x_6897__boxed_2471_ = lean_unbox(v___x_2468_);
v_res_2472_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_6897__boxed_2471_, v_x1_2469_, v_x2_2470_);
v_r_2473_ = lean_box(v_res_2472_);
return v_r_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object* v_hi_2474_, lean_object* v_pivot_2475_, lean_object* v_as_2476_, lean_object* v_i_2477_, lean_object* v_k_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_nat_dec_lt(v_k_2478_, v_hi_2474_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v_k_2478_);
lean_dec(v_pivot_2475_);
v___x_2480_ = lean_array_fswap(v_as_2476_, v_i_2477_, v_hi_2474_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_i_2477_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2482_ = lean_array_fget_borrowed(v_as_2476_, v_k_2478_);
lean_inc(v___x_2482_);
v___x_2483_ = l_Lean_Name_toString(v___x_2482_, v___x_2479_);
lean_inc(v_pivot_2475_);
v___x_2484_ = l_Lean_Name_toString(v_pivot_2475_, v___x_2479_);
v___x_2485_ = lean_string_dec_lt(v___x_2483_, v___x_2484_);
lean_dec_ref(v___x_2484_);
lean_dec_ref(v___x_2483_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_k_2478_, v___x_2486_);
lean_dec(v_k_2478_);
v_k_2478_ = v___x_2487_;
goto _start;
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2489_ = lean_array_fswap(v_as_2476_, v_i_2477_, v_k_2478_);
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_i_2477_, v___x_2490_);
lean_dec(v_i_2477_);
v___x_2492_ = lean_nat_add(v_k_2478_, v___x_2490_);
lean_dec(v_k_2478_);
v_as_2476_ = v___x_2489_;
v_i_2477_ = v___x_2491_;
v_k_2478_ = v___x_2492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_hi_2494_, lean_object* v_pivot_2495_, lean_object* v_as_2496_, lean_object* v_i_2497_, lean_object* v_k_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2494_, v_pivot_2495_, v_as_2496_, v_i_2497_, v_k_2498_);
lean_dec(v_hi_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_n_2500_, lean_object* v_as_2501_, lean_object* v_lo_2502_, lean_object* v_hi_2503_){
_start:
{
lean_object* v___y_2505_; uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_lt(v_lo_2502_, v_hi_2503_);
if (v___x_2515_ == 0)
{
lean_dec(v_lo_2502_);
return v_as_2501_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_mid_2518_; lean_object* v___y_2520_; lean_object* v___y_2526_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2516_ = lean_nat_add(v_lo_2502_, v_hi_2503_);
v___x_2517_ = lean_unsigned_to_nat(1u);
v_mid_2518_ = lean_nat_shiftr(v___x_2516_, v___x_2517_);
lean_dec(v___x_2516_);
v___x_2531_ = lean_array_fget_borrowed(v_as_2501_, v_mid_2518_);
v___x_2532_ = lean_array_fget_borrowed(v_as_2501_, v_lo_2502_);
lean_inc(v___x_2532_);
lean_inc(v___x_2531_);
v___x_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2515_, v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
v___y_2526_ = v_as_2501_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_array_fswap(v_as_2501_, v_lo_2502_, v_mid_2518_);
v___y_2526_ = v___x_2534_;
goto v___jp_2525_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = lean_array_fget_borrowed(v___y_2520_, v_mid_2518_);
v___x_2522_ = lean_array_fget_borrowed(v___y_2520_, v_hi_2503_);
lean_inc(v___x_2522_);
lean_inc(v___x_2521_);
v___x_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2515_, v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_dec(v_mid_2518_);
v___y_2505_ = v___y_2520_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_array_fswap(v___y_2520_, v_mid_2518_, v_hi_2503_);
lean_dec(v_mid_2518_);
v___y_2505_ = v___x_2524_;
goto v___jp_2504_;
}
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2527_ = lean_array_fget_borrowed(v___y_2526_, v_hi_2503_);
v___x_2528_ = lean_array_fget_borrowed(v___y_2526_, v_lo_2502_);
lean_inc(v___x_2528_);
lean_inc(v___x_2527_);
v___x_2529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2515_, v___x_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
v___y_2520_ = v___y_2526_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_array_fswap(v___y_2526_, v_lo_2502_, v_hi_2503_);
v___y_2520_ = v___x_2530_;
goto v___jp_2519_;
}
}
}
v___jp_2504_:
{
lean_object* v_pivot_2506_; lean_object* v___x_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; uint8_t v___x_2510_; 
v_pivot_2506_ = lean_array_fget(v___y_2505_, v_hi_2503_);
lean_inc_n(v_lo_2502_, 2);
v___x_2507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2503_, v_pivot_2506_, v___y_2505_, v_lo_2502_, v_lo_2502_);
v_fst_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_fst_2508_);
v_snd_2509_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2507_);
v___x_2510_ = lean_nat_dec_le(v_hi_2503_, v_fst_2508_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2500_, v_snd_2509_, v_lo_2502_, v_fst_2508_);
v___x_2512_ = lean_unsigned_to_nat(1u);
v___x_2513_ = lean_nat_add(v_fst_2508_, v___x_2512_);
lean_dec(v_fst_2508_);
v_as_2501_ = v___x_2511_;
v_lo_2502_ = v___x_2513_;
goto _start;
}
else
{
lean_dec(v_fst_2508_);
lean_dec(v_lo_2502_);
return v_snd_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_n_2535_, lean_object* v_as_2536_, lean_object* v_lo_2537_, lean_object* v_hi_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2535_, v_as_2536_, v_lo_2537_, v_hi_2538_);
lean_dec(v_hi_2538_);
lean_dec(v_n_2535_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2540_, lean_object* v_x_2541_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v_k_2543_; lean_object* v_l_2544_; lean_object* v_r_2545_; lean_object* v___x_2546_; lean_object* v_a_2547_; lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_k_2543_ = lean_ctor_get(v_x_2541_, 1);
lean_inc(v_k_2543_);
v_l_2544_ = lean_ctor_get(v_x_2541_, 3);
lean_inc(v_l_2544_);
v_r_2545_ = lean_ctor_get(v_x_2541_, 4);
lean_inc(v_r_2545_);
lean_dec_ref_known(v_x_2541_, 5);
v___x_2546_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2540_, v_l_2544_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
v_a_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2548_);
lean_dec(v_a_2547_);
v___x_2549_ = l_Lean_NameSet_insert(v_a_2548_, v_k_2543_);
v_init_2540_ = v___x_2549_;
v_x_2541_ = v_r_2545_;
goto _start;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_init_2540_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2553_, lean_object* v_x_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2553_, v_x_2554_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
lean_object* v_k_2559_; lean_object* v_l_2560_; lean_object* v_r_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_k_2559_ = lean_ctor_get(v_x_2558_, 1);
lean_inc(v_k_2559_);
v_l_2560_ = lean_ctor_get(v_x_2558_, 3);
lean_inc(v_l_2560_);
v_r_2561_ = lean_ctor_get(v_x_2558_, 4);
lean_inc(v_r_2561_);
lean_dec_ref_known(v_x_2558_, 5);
v___x_2562_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2557_, v_l_2560_);
v___x_2563_ = lean_array_push(v___x_2562_, v_k_2559_);
v_init_2557_ = v___x_2563_;
v_x_2558_ = v_r_2561_;
goto _start;
}
else
{
return v_init_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___y_2569_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_env_2598_; lean_object* v___x_2599_; lean_object* v_toEnvExtension_2600_; lean_object* v_asyncMode_2601_; lean_object* v_found_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v_a_2606_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_a_2625_; lean_object* v_a_2626_; 
v___x_2595_ = lean_box(1);
v___x_2596_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
v___x_2597_ = lean_st_ref_get(v___y_2566_);
v_env_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_ref_n(v_env_2598_, 2);
lean_dec(v___x_2597_);
v___x_2599_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2600_ = lean_ctor_get(v___x_2599_, 0);
v_asyncMode_2601_ = lean_ctor_get(v_toEnvExtension_2600_, 2);
v_found_2602_ = l_Lean_NameSet_empty;
v___x_2603_ = lean_box(0);
v___x_2604_ = 0;
v___x_2623_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2595_, v___x_2599_, v_env_2598_, v_asyncMode_2601_, v___x_2603_, v___x_2604_);
v___x_2624_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2602_, v___x_2623_);
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref(v___x_2624_);
v_a_2626_ = lean_ctor_get(v_a_2625_, 0);
lean_inc(v_a_2626_);
lean_dec(v_a_2625_);
v_a_2606_ = v_a_2626_;
goto v___jp_2605_;
v___jp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_array_to_list(v___y_2569_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
v___jp_2572_:
{
lean_object* v___x_2577_; 
v___x_2577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2574_, v___y_2573_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec(v___y_2574_);
v___y_2569_ = v___x_2577_;
goto v___jp_2568_;
}
v___jp_2578_:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_nat_dec_le(v___y_2582_, v___y_2581_);
if (v___x_2583_ == 0)
{
lean_dec(v___y_2581_);
lean_inc(v___y_2582_);
v___y_2573_ = v___y_2579_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___y_2582_;
v___y_2576_ = v___y_2582_;
goto v___jp_2572_;
}
else
{
v___y_2573_ = v___y_2579_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___y_2582_;
v___y_2576_ = v___y_2581_;
goto v___jp_2572_;
}
}
v___jp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2587_ = lean_mk_empty_array_with_capacity(v___y_2586_);
lean_dec(v___y_2586_);
v___x_2588_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2587_, v___y_2585_);
v___x_2589_ = lean_array_get_size(v___x_2588_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_nat_dec_eq(v___x_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = lean_unsigned_to_nat(1u);
v___x_2593_ = lean_nat_sub(v___x_2589_, v___x_2592_);
v___x_2594_ = lean_nat_dec_le(v___x_2590_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_inc(v___x_2593_);
v___y_2579_ = v___x_2588_;
v___y_2580_ = v___x_2589_;
v___y_2581_ = v___x_2593_;
v___y_2582_ = v___x_2593_;
goto v___jp_2578_;
}
else
{
v___y_2579_ = v___x_2588_;
v___y_2580_ = v___x_2589_;
v___y_2581_ = v___x_2593_;
v___y_2582_ = v___x_2590_;
goto v___jp_2578_;
}
}
else
{
v___y_2569_ = v___x_2588_;
goto v___jp_2568_;
}
}
v___jp_2605_:
{
lean_object* v___x_2607_; lean_object* v_importedEntries_2608_; size_t v_sz_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2607_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2596_, v_toEnvExtension_2600_, v_env_2598_, v_asyncMode_2601_, v___x_2603_, v___x_2604_);
v_importedEntries_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc_ref(v_importedEntries_2608_);
lean_dec(v___x_2607_);
v_sz_2609_ = lean_array_size(v_importedEntries_2608_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2608_, v_sz_2609_, v___x_2610_, v_a_2606_, v___y_2565_, v___y_2566_);
lean_dec_ref(v_importedEntries_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
if (lean_obj_tag(v_a_2612_) == 0)
{
lean_object* v_size_2613_; 
v_size_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_size_2613_);
v___y_2585_ = v_a_2612_;
v___y_2586_ = v_size_2613_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_unsigned_to_nat(0u);
v___y_2585_ = v_a_2612_;
v___y_2586_ = v___x_2614_;
goto v___jp_2584_;
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2611_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2611_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2630_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2633_ = l_Lean_stringToMessageData(v___x_2632_);
return v___x_2633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2636_ = l_Lean_stringToMessageData(v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2639_ = l_Lean_stringToMessageData(v___x_2638_);
return v___x_2639_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2649_ = l_Lean_MessageData_ofFormat(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2654_ = l_Lean_MessageData_ofFormat(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2658_, uint8_t v___x_2659_, lean_object* v_as_2660_, size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_a_2668_; uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2662_, v_sz_2661_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec(v_decl_2658_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2663_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v_a_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_unsigned_to_nat(1u);
v_a_2678_ = lean_array_uget_borrowed(v_as_2660_, v_i_2662_);
v___x_2679_ = l_Lean_TSyntax_getId(v_a_2678_);
lean_inc(v___x_2679_);
v___x_2680_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2679_, v___y_2665_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
if (lean_obj_tag(v_a_2681_) == 1)
{
lean_object* v___x_2682_; lean_object* v_env_2683_; lean_object* v_nextMacroScope_2684_; lean_object* v_ngen_2685_; lean_object* v_auxDeclNGen_2686_; lean_object* v_traceState_2687_; lean_object* v_recordedDeps_2688_; lean_object* v_messages_2689_; lean_object* v_infoState_2690_; lean_object* v_snapshotTasks_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref_known(v_a_2681_, 1);
v___x_2682_ = lean_st_ref_take(v___y_2665_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
v_nextMacroScope_2684_ = lean_ctor_get(v___x_2682_, 1);
v_ngen_2685_ = lean_ctor_get(v___x_2682_, 2);
v_auxDeclNGen_2686_ = lean_ctor_get(v___x_2682_, 3);
v_traceState_2687_ = lean_ctor_get(v___x_2682_, 4);
v_recordedDeps_2688_ = lean_ctor_get(v___x_2682_, 6);
v_messages_2689_ = lean_ctor_get(v___x_2682_, 7);
v_infoState_2690_ = lean_ctor_get(v___x_2682_, 8);
v_snapshotTasks_2691_ = lean_ctor_get(v___x_2682_, 9);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v___x_2682_, 5);
lean_dec(v_unused_2713_);
v___x_2693_ = v___x_2682_;
v_isShared_2694_ = v_isSharedCheck_2712_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snapshotTasks_2691_);
lean_inc(v_infoState_2690_);
lean_inc(v_messages_2689_);
lean_inc(v_recordedDeps_2688_);
lean_inc(v_traceState_2687_);
lean_inc(v_auxDeclNGen_2686_);
lean_inc(v_ngen_2685_);
lean_inc(v_nextMacroScope_2684_);
lean_inc(v_env_2683_);
lean_dec(v___x_2682_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2712_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___y_2696_; lean_object* v___x_2702_; lean_object* v_toEnvExtension_2703_; lean_object* v_addEntryFn_2704_; lean_object* v_asyncMode_2705_; uint8_t v_logWrites_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; 
v___x_2702_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2703_ = lean_ctor_get(v___x_2702_, 0);
v_addEntryFn_2704_ = lean_ctor_get(v___x_2702_, 3);
v_asyncMode_2705_ = lean_ctor_get(v_toEnvExtension_2703_, 2);
v_logWrites_2706_ = lean_ctor_get_uint8(v_toEnvExtension_2703_, sizeof(void*)*6);
lean_inc(v_decl_2658_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_decl_2658_);
lean_ctor_set(v___x_2707_, 1, v___x_2679_);
lean_inc(v_addEntryFn_2704_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2708_, 0, v_addEntryFn_2704_);
lean_closure_set(v___f_2708_, 1, v___x_2707_);
if (v_logWrites_2706_ == 0)
{
lean_object* v___x_2709_; 
lean_inc_ref(v_toEnvExtension_2703_);
v___x_2709_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2703_, v_env_2683_, v___f_2708_, v_asyncMode_2705_, v___x_2675_, v___x_2659_);
v___y_2696_ = v___x_2709_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_inc_ref_n(v_toEnvExtension_2703_, 2);
v___x_2710_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2703_, v_env_2683_);
lean_dec_ref(v_env_2683_);
v___x_2711_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2703_, v___x_2710_, v___f_2708_, v_asyncMode_2705_, v___x_2675_, v___x_2659_);
v___y_2696_ = v___x_2711_;
goto v___jp_2695_;
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 5, v___x_2697_);
lean_ctor_set(v___x_2693_, 0, v___y_2696_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___y_2696_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_nextMacroScope_2684_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_ngen_2685_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_auxDeclNGen_2686_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_traceState_2687_);
lean_ctor_set(v_reuseFailAlloc_2701_, 5, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2701_, 6, v_recordedDeps_2688_);
lean_ctor_set(v_reuseFailAlloc_2701_, 7, v_messages_2689_);
lean_ctor_set(v_reuseFailAlloc_2701_, 8, v_infoState_2690_);
lean_ctor_set(v_reuseFailAlloc_2701_, 9, v_snapshotTasks_2691_);
v___x_2699_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_st_ref_put(v___y_2665_, v___x_2699_);
v_a_2668_ = v___x_2674_;
goto v___jp_2667_;
}
}
}
}
else
{
lean_object* v___x_2714_; 
lean_dec(v_a_2681_);
v___x_2714_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___y_2717_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2729_ = l_List_lengthTR___redArg(v_a_2715_);
v___x_2730_ = lean_nat_dec_eq(v___x_2729_, v___x_2676_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_nat_dec_eq(v___x_2729_, v___x_2677_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = lean_unsigned_to_nat(10u);
v___x_2733_ = lean_nat_dec_lt(v___x_2729_, v___x_2732_);
lean_dec(v___x_2729_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_2715_);
v___x_2736_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_2715_, v_a_2715_, v___x_2732_, v___x_2735_);
lean_dec(v_a_2715_);
v___x_2737_ = lean_box(0);
v___x_2738_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_2736_, v___x_2737_);
v___x_2739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2740_ = l_Lean_MessageData_joinSep(v___x_2738_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2734_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___y_2717_ = v___x_2743_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2745_ = lean_box(0);
v___x_2746_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2715_, v___x_2745_);
v___x_2747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2748_ = l_Lean_MessageData_joinSep(v___x_2746_, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2744_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___y_2717_ = v___x_2749_;
goto v___jp_2716_;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v___x_2729_);
v___x_2750_ = lean_box(0);
v___x_2751_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2715_, v___x_2750_);
v___x_2752_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2753_ = l_Lean_MessageData_joinSep(v___x_2751_, v___x_2752_);
v___y_2717_ = v___x_2753_;
goto v___jp_2716_;
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v___x_2729_);
lean_dec(v_a_2715_);
v___x_2754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_2717_ = v___x_2754_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___y_2717_);
v___x_2720_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_2723_ = l_Lean_MessageData_ofName(v___x_2679_);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v___x_2721_);
v___x_2728_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_a_2678_, v___x_2727_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_dec_ref_known(v___x_2728_, 1);
v_a_2668_ = v___x_2674_;
goto v___jp_2667_;
}
else
{
lean_dec(v_decl_2658_);
return v___x_2728_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v___x_2679_);
lean_dec(v_decl_2658_);
v_a_2755_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2714_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2714_);
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
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
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
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v___x_2679_);
lean_dec(v_decl_2658_);
v_a_2763_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2680_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2680_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
v___jp_2667_:
{
size_t v___x_2669_; size_t v___x_2670_; 
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2662_, v___x_2669_);
v_i_2662_ = v___x_2670_;
v_b_2663_ = v_a_2668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_2771_, lean_object* v___x_2772_, lean_object* v_as_2773_, lean_object* v_sz_2774_, lean_object* v_i_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
uint8_t v___x_7245__boxed_2780_; size_t v_sz_boxed_2781_; size_t v_i_boxed_2782_; lean_object* v_res_2783_; 
v___x_7245__boxed_2780_ = lean_unbox(v___x_2772_);
v_sz_boxed_2781_ = lean_unbox_usize(v_sz_2774_);
lean_dec(v_sz_2774_);
v_i_boxed_2782_ = lean_unbox_usize(v_i_2775_);
lean_dec(v_i_2775_);
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2771_, v___x_7245__boxed_2780_, v_as_2773_, v_sz_boxed_2781_, v_i_boxed_2782_, v_b_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec_ref(v_as_2773_);
return v_res_2783_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v___x_2789_, lean_object* v_name_2790_, lean_object* v_decl_2791_, lean_object* v_stx_2792_, uint8_t v_kind_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; uint8_t v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = 0;
v___x_2860_ = l_Lean_instBEqAttributeKind_beq(v_kind_2793_, v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
lean_dec(v_stx_2792_);
lean_dec(v_decl_2791_);
lean_dec_ref(v___x_2789_);
lean_dec_ref(v___x_2788_);
lean_dec_ref(v___x_2787_);
v___x_2861_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_2790_, v_kind_2793_, v___y_2794_, v___y_2795_);
return v___x_2861_;
}
else
{
goto v___jp_2833_;
}
v___jp_2797_:
{
lean_object* v___x_2802_; size_t v_sz_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_box(0);
v_sz_2803_ = lean_array_size(v___y_2799_);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2791_, v___y_2798_, v___y_2799_, v_sz_2803_, v___x_2804_, v___x_2802_, v___y_2800_, v___y_2801_);
lean_dec_ref(v___y_2799_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2812_ == 0)
{
lean_object* v_unused_2813_; 
v_unused_2813_ = lean_ctor_get(v___x_2805_, 0);
lean_dec(v_unused_2813_);
v___x_2807_ = v___x_2805_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v___x_2805_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2802_);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2802_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
return v___x_2805_;
}
}
v___jp_2814_:
{
lean_object* v___x_2819_; lean_object* v_env_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_st_ref_get(v___y_2818_);
v_env_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc_ref(v_env_2820_);
lean_dec(v___x_2819_);
lean_inc(v_decl_2791_);
v___x_2821_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_2820_, v_decl_2791_);
if (lean_obj_tag(v___x_2821_) == 1)
{
lean_object* v_val_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec_ref(v___y_2816_);
v_val_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2824_ = 0;
v___x_2825_ = l_Lean_MessageData_ofConstName(v_decl_2791_, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2823_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_MessageData_ofConstName(v_val_2822_, v___x_2824_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2823_);
v___x_2832_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_2792_, v___x_2831_, v___y_2817_, v___y_2818_);
lean_dec(v_stx_2792_);
return v___x_2832_;
}
else
{
lean_dec(v___x_2821_);
lean_dec(v_stx_2792_);
v___y_2798_ = v___y_2815_;
v___y_2799_ = v___y_2816_;
v___y_2800_ = v___y_2817_;
v___y_2801_ = v___y_2818_;
goto v___jp_2797_;
}
}
v___jp_2833_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_2835_ = l_Lean_Name_mkStr4(v___x_2787_, v___x_2788_, v___x_2834_, v___x_2789_);
lean_inc(v_stx_2792_);
v___x_2836_ = l_Lean_Syntax_isOfKind(v_stx_2792_, v___x_2835_);
lean_dec(v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec(v_stx_2792_);
lean_dec(v_decl_2791_);
v___x_2837_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2838_ = l_Lean_MessageData_ofName(v_name_2790_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_2841_, v___y_2794_, v___y_2795_);
return v___x_2842_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v_tags_2845_; lean_object* v___x_2846_; lean_object* v_env_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; 
lean_dec(v_name_2790_);
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = l_Lean_Syntax_getArg(v_stx_2792_, v___x_2843_);
v_tags_2845_ = l_Lean_Syntax_getArgs(v___x_2844_);
lean_dec(v___x_2844_);
v___x_2846_ = lean_st_ref_get(v___y_2795_);
v_env_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2847_);
lean_dec(v___x_2846_);
v___x_2848_ = 0;
lean_inc(v_decl_2791_);
v___x_2849_ = l_Lean_Environment_find_x3f(v_env_2847_, v_decl_2791_, v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
v___y_2815_ = v___x_2836_;
v___y_2816_ = v_tags_2845_;
v___y_2817_ = v___y_2794_;
v___y_2818_ = v___y_2795_;
goto v___jp_2814_;
}
else
{
lean_object* v___x_2850_; lean_object* v_env_2851_; uint8_t v___x_2852_; 
lean_dec_ref_known(v___x_2849_, 1);
v___x_2850_ = lean_st_ref_get(v___y_2795_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_env_2851_);
lean_dec(v___x_2850_);
v___x_2852_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_2851_, v_decl_2791_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref(v_tags_2845_);
v___x_2853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2854_ = l_Lean_MessageData_ofConstName(v_decl_2791_, v___x_2848_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_2792_, v___x_2857_, v___y_2794_, v___y_2795_);
lean_dec(v_stx_2792_);
return v___x_2858_;
}
else
{
v___y_2815_ = v___x_2836_;
v___y_2816_ = v_tags_2845_;
v___y_2817_ = v___y_2794_;
v___y_2818_ = v___y_2795_;
goto v___jp_2814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v_name_2865_, lean_object* v_decl_2866_, lean_object* v_stx_2867_, lean_object* v_kind_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v_kind_boxed_2872_; lean_object* v_res_2873_; 
v_kind_boxed_2872_ = lean_unbox(v_kind_2868_);
v_res_2873_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_2862_, v___x_2863_, v___x_2864_, v_name_2865_, v_decl_2866_, v_stx_2867_, v_kind_boxed_2872_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_2908_ = l_Lean_registerBuiltinAttribute(v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2911_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_2921_, lean_object* v_k_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2921_, v_k_2922_, v_x_2923_, v_x_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_2927_, lean_object* v_k_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_2927_, v_k_2928_, v_x_2929_, v_x_2930_, v_x_2931_);
lean_dec_ref(v_k_2928_);
lean_dec_ref(v_as_2927_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_2933_, size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2933_, v_sz_2934_, v_i_2935_, v_b_2936_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_2941_, lean_object* v_sz_2942_, lean_object* v_i_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
size_t v_sz_boxed_2948_; size_t v_i_boxed_2949_; lean_object* v_res_2950_; 
v_sz_boxed_2948_ = lean_unbox_usize(v_sz_2942_);
lean_dec(v_sz_2942_);
v_i_boxed_2949_ = lean_unbox_usize(v_i_2943_);
lean_dec(v_i_2943_);
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_2941_, v_sz_boxed_2948_, v_i_boxed_2949_, v_b_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_as_2941_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_2951_, lean_object* v_t_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2951_, v_t_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_2954_, lean_object* v_as_2955_, lean_object* v_lo_2956_, lean_object* v_hi_2957_, lean_object* v_w_2958_, lean_object* v_hlo_2959_, lean_object* v_hhi_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2954_, v_as_2955_, v_lo_2956_, v_hi_2957_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_2962_, lean_object* v_as_2963_, lean_object* v_lo_2964_, lean_object* v_hi_2965_, lean_object* v_w_2966_, lean_object* v_hlo_2967_, lean_object* v_hhi_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_2962_, v_as_2963_, v_lo_2964_, v_hi_2965_, v_w_2966_, v_hlo_2967_, v_hhi_2968_);
lean_dec(v_hi_2965_);
lean_dec(v_n_2962_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_2970_, lean_object* v_x_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2970_, v_x_2971_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_2976_, lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_2976_, v_x_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object* v_n_2982_, lean_object* v_lo_2983_, lean_object* v_hi_2984_, lean_object* v_hhi_2985_, lean_object* v_pivot_2986_, lean_object* v_as_2987_, lean_object* v_i_2988_, lean_object* v_k_2989_, lean_object* v_ilo_2990_, lean_object* v_ik_2991_, lean_object* v_w_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2984_, v_pivot_2986_, v_as_2987_, v_i_2988_, v_k_2989_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object* v_n_2994_, lean_object* v_lo_2995_, lean_object* v_hi_2996_, lean_object* v_hhi_2997_, lean_object* v_pivot_2998_, lean_object* v_as_2999_, lean_object* v_i_3000_, lean_object* v_k_3001_, lean_object* v_ilo_3002_, lean_object* v_ik_3003_, lean_object* v_w_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(v_n_2994_, v_lo_2995_, v_hi_2996_, v_hhi_2997_, v_pivot_2998_, v_as_2999_, v_i_3000_, v_k_3001_, v_ilo_3002_, v_ik_3003_, v_w_3004_);
lean_dec(v_hi_2996_);
lean_dec(v_lo_2995_);
lean_dec(v_n_2994_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3008_, lean_object* v_x_3009_){
_start:
{
lean_object* v_fst_3010_; lean_object* v_snd_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_fst_3010_ = lean_ctor_get(v_x_3009_, 0);
lean_inc(v_fst_3010_);
v_snd_3011_ = lean_ctor_get(v_x_3009_, 1);
lean_inc(v_snd_3011_);
lean_dec_ref(v_x_3009_);
v___x_3012_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3013_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3008_, v_fst_3010_, v___x_3012_);
v___x_3014_ = lean_array_push(v___x_3013_, v_snd_3011_);
v___x_3015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3010_, v___x_3014_, v_es_3008_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3016_, lean_object* v_x_3017_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v_k_3018_; lean_object* v_v_3019_; lean_object* v_l_3020_; lean_object* v_r_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_k_3018_ = lean_ctor_get(v_x_3017_, 1);
v_v_3019_ = lean_ctor_get(v_x_3017_, 2);
v_l_3020_ = lean_ctor_get(v_x_3017_, 3);
v_r_3021_ = lean_ctor_get(v_x_3017_, 4);
v___x_3022_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3016_, v_l_3020_);
lean_inc(v_v_3019_);
lean_inc(v_k_3018_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_k_3018_);
lean_ctor_set(v___x_3023_, 1, v_v_3019_);
v___x_3024_ = lean_array_push(v___x_3022_, v___x_3023_);
v_init_3016_ = v___x_3024_;
v_x_3017_ = v_r_3021_;
goto _start;
}
else
{
return v_init_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3026_, v_x_3027_);
lean_dec(v_x_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3029_, lean_object* v_x2_3030_){
_start:
{
lean_object* v_fst_3031_; lean_object* v_fst_3032_; uint8_t v___x_3033_; 
v_fst_3031_ = lean_ctor_get(v_x1_3029_, 0);
v_fst_3032_ = lean_ctor_get(v_x2_3030_, 0);
v___x_3033_ = l_Lean_Name_quickLt(v_fst_3031_, v_fst_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3034_, lean_object* v_x2_3035_){
_start:
{
uint8_t v_res_3036_; lean_object* v_r_3037_; 
v_res_3036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3034_, v_x2_3035_);
lean_dec_ref(v_x2_3035_);
lean_dec_ref(v_x1_3034_);
v_r_3037_ = lean_box(v_res_3036_);
return v_r_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3038_, lean_object* v_pivot_3039_, lean_object* v_as_3040_, lean_object* v_i_3041_, lean_object* v_k_3042_){
_start:
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_nat_dec_lt(v_k_3042_, v_hi_3038_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec(v_k_3042_);
v___x_3044_ = lean_array_fswap(v_as_3040_, v_i_3041_, v_hi_3038_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_i_3041_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v_fst_3047_; lean_object* v_fst_3048_; uint8_t v___x_3049_; 
v___x_3046_ = lean_array_fget_borrowed(v_as_3040_, v_k_3042_);
v_fst_3047_ = lean_ctor_get(v___x_3046_, 0);
v_fst_3048_ = lean_ctor_get(v_pivot_3039_, 0);
v___x_3049_ = l_Lean_Name_quickLt(v_fst_3047_, v_fst_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_k_3042_, v___x_3050_);
lean_dec(v_k_3042_);
v_k_3042_ = v___x_3051_;
goto _start;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = lean_array_fswap(v_as_3040_, v_i_3041_, v_k_3042_);
v___x_3054_ = lean_unsigned_to_nat(1u);
v___x_3055_ = lean_nat_add(v_i_3041_, v___x_3054_);
lean_dec(v_i_3041_);
v___x_3056_ = lean_nat_add(v_k_3042_, v___x_3054_);
lean_dec(v_k_3042_);
v_as_3040_ = v___x_3053_;
v_i_3041_ = v___x_3055_;
v_k_3042_ = v___x_3056_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3058_, lean_object* v_pivot_3059_, lean_object* v_as_3060_, lean_object* v_i_3061_, lean_object* v_k_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3058_, v_pivot_3059_, v_as_3060_, v_i_3061_, v_k_3062_);
lean_dec_ref(v_pivot_3059_);
lean_dec(v_hi_3058_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3064_, lean_object* v_as_3065_, lean_object* v_lo_3066_, lean_object* v_hi_3067_){
_start:
{
lean_object* v___y_3069_; uint8_t v___x_3079_; 
v___x_3079_ = lean_nat_dec_lt(v_lo_3066_, v_hi_3067_);
if (v___x_3079_ == 0)
{
lean_dec(v_lo_3066_);
return v_as_3065_;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_mid_3082_; lean_object* v___y_3084_; lean_object* v___y_3090_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3080_ = lean_nat_add(v_lo_3066_, v_hi_3067_);
v___x_3081_ = lean_unsigned_to_nat(1u);
v_mid_3082_ = lean_nat_shiftr(v___x_3080_, v___x_3081_);
lean_dec(v___x_3080_);
v___x_3095_ = lean_array_fget_borrowed(v_as_3065_, v_mid_3082_);
v___x_3096_ = lean_array_fget_borrowed(v_as_3065_, v_lo_3066_);
v___x_3097_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
v___y_3090_ = v_as_3065_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_array_fswap(v_as_3065_, v_lo_3066_, v_mid_3082_);
v___y_3090_ = v___x_3098_;
goto v___jp_3089_;
}
v___jp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3085_ = lean_array_fget_borrowed(v___y_3084_, v_mid_3082_);
v___x_3086_ = lean_array_fget_borrowed(v___y_3084_, v_hi_3067_);
v___x_3087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3085_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_dec(v_mid_3082_);
v___y_3069_ = v___y_3084_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_array_fswap(v___y_3084_, v_mid_3082_, v_hi_3067_);
lean_dec(v_mid_3082_);
v___y_3069_ = v___x_3088_;
goto v___jp_3068_;
}
}
v___jp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = lean_array_fget_borrowed(v___y_3090_, v_hi_3067_);
v___x_3092_ = lean_array_fget_borrowed(v___y_3090_, v_lo_3066_);
v___x_3093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3091_, v___x_3092_);
if (v___x_3093_ == 0)
{
v___y_3084_ = v___y_3090_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_array_fswap(v___y_3090_, v_lo_3066_, v_hi_3067_);
v___y_3084_ = v___x_3094_;
goto v___jp_3083_;
}
}
}
v___jp_3068_:
{
lean_object* v_pivot_3070_; lean_object* v___x_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; uint8_t v___x_3074_; 
v_pivot_3070_ = lean_array_fget(v___y_3069_, v_hi_3067_);
lean_inc_n(v_lo_3066_, 2);
v___x_3071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3067_, v_pivot_3070_, v___y_3069_, v_lo_3066_, v_lo_3066_);
lean_dec(v_pivot_3070_);
v_fst_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_fst_3072_);
v_snd_3073_ = lean_ctor_get(v___x_3071_, 1);
lean_inc(v_snd_3073_);
lean_dec_ref(v___x_3071_);
v___x_3074_ = lean_nat_dec_le(v_hi_3067_, v_fst_3072_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3064_, v_snd_3073_, v_lo_3066_, v_fst_3072_);
v___x_3076_ = lean_unsigned_to_nat(1u);
v___x_3077_ = lean_nat_add(v_fst_3072_, v___x_3076_);
lean_dec(v_fst_3072_);
v_as_3065_ = v___x_3075_;
v_lo_3066_ = v___x_3077_;
goto _start;
}
else
{
lean_dec(v_fst_3072_);
lean_dec(v_lo_3066_);
return v_snd_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3099_, lean_object* v_as_3100_, lean_object* v_lo_3101_, lean_object* v_hi_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3099_, v_as_3100_, v_lo_3101_, v_hi_3102_);
lean_dec(v_hi_3102_);
lean_dec(v_n_3099_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3106_, lean_object* v_s_3107_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___x_3117_; 
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3110_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3109_, v_s_3107_);
v___x_3111_ = lean_array_get_size(v___x_3110_);
v___x_3117_ = lean_nat_dec_eq(v___x_3111_, v___x_3108_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___y_3121_; uint8_t v___x_3123_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_sub(v___x_3111_, v___x_3118_);
v___x_3123_ = lean_nat_dec_le(v___x_3108_, v___x_3119_);
if (v___x_3123_ == 0)
{
lean_inc(v___x_3119_);
v___y_3121_ = v___x_3119_;
goto v___jp_3120_;
}
else
{
v___y_3121_ = v___x_3108_;
goto v___jp_3120_;
}
v___jp_3120_:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_le(v___y_3121_, v___x_3119_);
if (v___x_3122_ == 0)
{
lean_dec(v___x_3119_);
lean_inc(v___y_3121_);
v___y_3113_ = v___y_3121_;
v___y_3114_ = v___y_3121_;
goto v___jp_3112_;
}
else
{
v___y_3113_ = v___y_3121_;
v___y_3114_ = v___x_3119_;
goto v___jp_3112_;
}
}
}
else
{
lean_object* v___x_3124_; 
lean_inc_ref_n(v___x_3110_, 2);
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3110_);
lean_ctor_set(v___x_3124_, 1, v___x_3110_);
lean_ctor_set(v___x_3124_, 2, v___x_3110_);
return v___x_3124_;
}
v___jp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3111_, v___x_3110_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_inc_ref_n(v___x_3115_, 2);
v___x_3116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
lean_ctor_set(v___x_3116_, 2, v___x_3115_);
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3125_, lean_object* v_s_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3125_, v_s_3126_);
lean_dec(v_s_3126_);
lean_dec_ref(v_x_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3128_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3131_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3130_, v_es_3128_);
v___x_3132_ = lean_array_get_size(v___x_3131_);
v___x_3133_ = lean_nat_dec_eq(v___x_3132_, v___x_3129_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___y_3137_; uint8_t v___x_3141_; 
v___x_3134_ = lean_unsigned_to_nat(1u);
v___x_3135_ = lean_nat_sub(v___x_3132_, v___x_3134_);
v___x_3141_ = lean_nat_dec_le(v___x_3129_, v___x_3135_);
if (v___x_3141_ == 0)
{
lean_inc(v___x_3135_);
v___y_3137_ = v___x_3135_;
goto v___jp_3136_;
}
else
{
v___y_3137_ = v___x_3129_;
goto v___jp_3136_;
}
v___jp_3136_:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_le(v___y_3137_, v___x_3135_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_dec(v___x_3135_);
lean_inc(v___y_3137_);
v___x_3139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3132_, v___x_3131_, v___y_3137_, v___y_3137_);
lean_dec(v___y_3137_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3132_, v___x_3131_, v___y_3137_, v___x_3135_);
lean_dec(v___x_3135_);
return v___x_3140_;
}
}
}
else
{
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3142_);
lean_dec(v_es_3142_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3144_, lean_object* v_x_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3144_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3149_, lean_object* v_x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3149_, v_x_3150_, v___y_3151_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v_x_3150_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3181_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3184_, lean_object* v_t_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3184_, v_t_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3187_, lean_object* v_t_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3187_, v_t_3188_);
lean_dec(v_t_3188_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3190_, lean_object* v_as_3191_, lean_object* v_lo_3192_, lean_object* v_hi_3193_, lean_object* v_w_3194_, lean_object* v_hlo_3195_, lean_object* v_hhi_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3190_, v_as_3191_, v_lo_3192_, v_hi_3193_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3198_, lean_object* v_as_3199_, lean_object* v_lo_3200_, lean_object* v_hi_3201_, lean_object* v_w_3202_, lean_object* v_hlo_3203_, lean_object* v_hhi_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3198_, v_as_3199_, v_lo_3200_, v_hi_3201_, v_w_3202_, v_hlo_3203_, v_hhi_3204_);
lean_dec(v_hi_3201_);
lean_dec(v_n_3198_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3206_, lean_object* v_lo_3207_, lean_object* v_hi_3208_, lean_object* v_hhi_3209_, lean_object* v_pivot_3210_, lean_object* v_as_3211_, lean_object* v_i_3212_, lean_object* v_k_3213_, lean_object* v_ilo_3214_, lean_object* v_ik_3215_, lean_object* v_w_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3208_, v_pivot_3210_, v_as_3211_, v_i_3212_, v_k_3213_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3218_, lean_object* v_lo_3219_, lean_object* v_hi_3220_, lean_object* v_hhi_3221_, lean_object* v_pivot_3222_, lean_object* v_as_3223_, lean_object* v_i_3224_, lean_object* v_k_3225_, lean_object* v_ilo_3226_, lean_object* v_ik_3227_, lean_object* v_w_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(v_n_3218_, v_lo_3219_, v_hi_3220_, v_hhi_3221_, v_pivot_3222_, v_as_3223_, v_i_3224_, v_k_3225_, v_ilo_3226_, v_ik_3227_, v_w_3228_);
lean_dec_ref(v_pivot_3222_);
lean_dec(v_hi_3220_);
lean_dec(v_lo_3219_);
lean_dec(v_n_3218_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3230_, lean_object* v_k_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v_m_3236_; lean_object* v_a_3237_; uint8_t v___x_3238_; 
v___x_3234_ = lean_nat_add(v_x_3232_, v_x_3233_);
v___x_3235_ = lean_unsigned_to_nat(1u);
v_m_3236_ = lean_nat_shiftr(v___x_3234_, v___x_3235_);
lean_dec(v___x_3234_);
v_a_3237_ = lean_array_fget_borrowed(v_as_3230_, v_m_3236_);
v___x_3238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3237_, v_k_3231_);
if (v___x_3238_ == 0)
{
uint8_t v___x_3239_; 
lean_dec(v_x_3233_);
v___x_3239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3231_, v_a_3237_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec(v_m_3236_);
lean_dec(v_x_3232_);
lean_inc(v_a_3237_);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_a_3237_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = lean_unsigned_to_nat(0u);
v___x_3242_ = lean_nat_dec_eq(v_m_3236_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_nat_sub(v_m_3236_, v___x_3235_);
lean_dec(v_m_3236_);
v___x_3244_ = lean_nat_dec_lt(v___x_3243_, v_x_3232_);
if (v___x_3244_ == 0)
{
v_x_3233_ = v___x_3243_;
goto _start;
}
else
{
lean_object* v___x_3246_; 
lean_dec(v___x_3243_);
lean_dec(v_x_3232_);
v___x_3246_ = lean_box(0);
return v___x_3246_;
}
}
else
{
lean_object* v___x_3247_; 
lean_dec(v_m_3236_);
lean_dec(v_x_3232_);
v___x_3247_ = lean_box(0);
return v___x_3247_;
}
}
}
else
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
lean_dec(v_x_3232_);
v___x_3248_ = lean_nat_add(v_m_3236_, v___x_3235_);
lean_dec(v_m_3236_);
v___x_3249_ = lean_nat_dec_le(v___x_3248_, v_x_3233_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_dec(v___x_3248_);
lean_dec(v_x_3233_);
v___x_3250_ = lean_box(0);
return v___x_3250_;
}
else
{
v_x_3232_ = v___x_3248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3252_, lean_object* v_k_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3252_, v_k_3253_, v_x_3254_, v_x_3255_);
lean_dec_ref(v_k_3253_);
lean_dec_ref(v_as_3252_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3257_, lean_object* v_as_3258_, size_t v_sz_3259_, size_t v_i_3260_, lean_object* v_b_3261_){
_start:
{
lean_object* v_a_3263_; uint8_t v___x_3267_; 
v___x_3267_ = lean_usize_dec_lt(v_i_3260_, v_sz_3259_);
if (v___x_3267_ == 0)
{
lean_dec(v_tactic_3257_);
return v_b_3261_;
}
else
{
lean_object* v___x_3268_; lean_object* v_a_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3268_ = lean_unsigned_to_nat(0u);
v_a_3269_ = lean_array_uget_borrowed(v_as_3258_, v_i_3260_);
v___x_3270_ = lean_array_get_size(v_a_3269_);
v___x_3271_ = lean_nat_dec_lt(v___x_3268_, v___x_3270_);
if (v___x_3271_ == 0)
{
v_a_3263_ = v_b_3261_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3272_ = lean_unsigned_to_nat(1u);
v___x_3273_ = lean_nat_sub(v___x_3270_, v___x_3272_);
v___x_3274_ = lean_nat_dec_le(v___x_3268_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec(v___x_3273_);
v_a_3263_ = v_b_3261_;
goto v___jp_3262_;
}
else
{
lean_object* v_extensions_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_extensions_3275_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3257_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_tactic_3257_);
lean_ctor_set(v___x_3276_, 1, v_extensions_3275_);
v___x_3277_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3269_, v___x_3276_, v___x_3268_, v___x_3273_);
lean_dec_ref_known(v___x_3276_, 2);
if (lean_obj_tag(v___x_3277_) == 1)
{
lean_object* v_val_3278_; lean_object* v_snd_3279_; lean_object* v___x_3280_; 
v_val_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_val_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v_snd_3279_ = lean_ctor_get(v_val_3278_, 1);
lean_inc(v_snd_3279_);
lean_dec(v_val_3278_);
v___x_3280_ = l_Array_append___redArg(v_b_3261_, v_snd_3279_);
lean_dec(v_snd_3279_);
v_a_3263_ = v___x_3280_;
goto v___jp_3262_;
}
else
{
lean_dec(v___x_3277_);
v_a_3263_ = v_b_3261_;
goto v___jp_3262_;
}
}
}
}
v___jp_3262_:
{
size_t v___x_3264_; size_t v___x_3265_; 
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3260_, v___x_3264_);
v_i_3260_ = v___x_3265_;
v_b_3261_ = v_a_3263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3281_, lean_object* v_as_3282_, lean_object* v_sz_3283_, lean_object* v_i_3284_, lean_object* v_b_3285_){
_start:
{
size_t v_sz_boxed_3286_; size_t v_i_boxed_3287_; lean_object* v_res_3288_; 
v_sz_boxed_3286_ = lean_unbox_usize(v_sz_3283_);
lean_dec(v_sz_3283_);
v_i_boxed_3287_ = lean_unbox_usize(v_i_3284_);
lean_dec(v_i_3284_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3281_, v_as_3282_, v_sz_boxed_3286_, v_i_boxed_3287_, v_b_3285_);
lean_dec_ref(v_as_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3289_, lean_object* v_tactic_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v_toEnvExtension_3292_; lean_object* v_asyncMode_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v_importedEntries_3299_; lean_object* v_extensions_3300_; size_t v_sz_3301_; size_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3291_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3292_ = lean_ctor_get(v___x_3291_, 0);
v_asyncMode_3293_ = lean_ctor_get(v_toEnvExtension_3292_, 2);
v___x_3294_ = lean_box(1);
v___x_3295_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
v___x_3296_ = lean_box(0);
v___x_3297_ = 0;
lean_inc_ref(v_env_3289_);
v___x_3298_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3295_, v_toEnvExtension_3292_, v_env_3289_, v_asyncMode_3293_, v___x_3296_, v___x_3297_);
v_importedEntries_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref(v_importedEntries_3299_);
lean_dec(v___x_3298_);
v_extensions_3300_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3301_ = lean_array_size(v_importedEntries_3299_);
v___x_3302_ = ((size_t)0ULL);
lean_inc(v_tactic_3290_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3290_, v_importedEntries_3299_, v_sz_3301_, v___x_3302_, v_extensions_3300_);
lean_dec_ref(v_importedEntries_3299_);
v___x_3304_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3294_, v___x_3291_, v_env_3289_, v_asyncMode_3293_, v___x_3296_, v___x_3297_);
v___x_3305_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3304_, v_tactic_3290_);
lean_dec(v_tactic_3290_);
lean_dec(v___x_3304_);
if (lean_obj_tag(v___x_3305_) == 1)
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = l_Array_append___redArg(v___x_3303_, v_val_3306_);
lean_dec(v_val_3306_);
return v___x_3307_;
}
else
{
lean_dec(v___x_3305_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3308_, lean_object* v_k_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3308_, v_k_3309_, v_x_3310_, v_x_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3314_, lean_object* v_k_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3314_, v_k_3315_, v_x_3316_, v_x_3317_, v_x_3318_);
lean_dec_ref(v_k_3315_);
lean_dec_ref(v_as_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3320_, lean_object* v_pos_3321_){
_start:
{
lean_object* v_str_3322_; lean_object* v_startInclusive_3323_; lean_object* v_endExclusive_3324_; lean_object* v___x_3325_; lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v_decide_3336_; 
v_str_3322_ = lean_ctor_get(v_s_3320_, 0);
v_startInclusive_3323_ = lean_ctor_get(v_s_3320_, 1);
v_endExclusive_3324_ = lean_ctor_get(v_s_3320_, 2);
v___x_3325_ = lean_nat_add(v_startInclusive_3323_, v_pos_3321_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_nat_sub(v_endExclusive_3324_, v___x_3325_);
v_decide_3336_ = lean_nat_dec_eq(v___x_3334_, v___x_3335_);
lean_dec(v___x_3335_);
if (v_decide_3336_ == 0)
{
uint32_t v___x_3337_; uint32_t v___x_3338_; uint8_t v___x_3339_; 
v___x_3337_ = lean_string_utf8_get_fast(v_str_3322_, v___x_3325_);
v___x_3338_ = 32;
v___x_3339_ = lean_uint32_dec_eq(v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
uint32_t v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = 9;
v___x_3341_ = lean_uint32_dec_eq(v___x_3337_, v___x_3340_);
if (v___x_3341_ == 0)
{
uint32_t v___x_3342_; uint8_t v___x_3343_; 
v___x_3342_ = 13;
v___x_3343_ = lean_uint32_dec_eq(v___x_3337_, v___x_3342_);
if (v___x_3343_ == 0)
{
uint32_t v___x_3344_; uint8_t v___x_3345_; 
v___x_3344_ = 10;
v___x_3345_ = lean_uint32_dec_eq(v___x_3337_, v___x_3344_);
if (v___x_3345_ == 0)
{
lean_dec(v___x_3325_);
return v_pos_3321_;
}
else
{
goto v___jp_3326_;
}
}
else
{
goto v___jp_3326_;
}
}
else
{
goto v___jp_3326_;
}
}
else
{
goto v___jp_3326_;
}
}
else
{
lean_dec(v___x_3325_);
return v_pos_3321_;
}
v___jp_3326_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3327_ = lean_string_utf8_next_fast(v_str_3322_, v___x_3325_);
v___x_3328_ = lean_nat_sub(v___x_3327_, v___x_3325_);
lean_dec(v___x_3325_);
v___x_3329_ = lean_nat_add(v_pos_3321_, v___x_3328_);
lean_dec(v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_nat_add(v_pos_3321_, v___x_3330_);
v___x_3332_ = lean_nat_dec_le(v___x_3331_, v___x_3329_);
lean_dec(v___x_3331_);
if (v___x_3332_ == 0)
{
lean_dec(v___x_3329_);
return v_pos_3321_;
}
else
{
lean_dec(v_pos_3321_);
v_pos_3321_ = v___x_3329_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3346_, lean_object* v_pos_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3346_, v_pos_3347_);
lean_dec_ref(v_s_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3351_){
_start:
{
lean_object* v___y_3353_; lean_object* v_str_3356_; lean_object* v_startInclusive_3357_; lean_object* v_endExclusive_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v_decide_3362_; 
v_str_3356_ = lean_ctor_get(v_str_3351_, 0);
v_startInclusive_3357_ = lean_ctor_get(v_str_3351_, 1);
v_endExclusive_3358_ = lean_ctor_get(v_str_3351_, 2);
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3351_, v___x_3359_);
v___x_3361_ = lean_nat_sub(v_endExclusive_3358_, v_startInclusive_3357_);
v_decide_3362_ = lean_nat_dec_eq(v___x_3360_, v___x_3361_);
lean_dec(v___x_3361_);
lean_dec(v___x_3360_);
if (v_decide_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3364_ = lean_string_utf8_extract_fast(v_str_3356_, v_startInclusive_3357_, v_endExclusive_3358_);
v___x_3365_ = lean_string_append(v___x_3363_, v___x_3364_);
lean_dec_ref(v___x_3364_);
v___y_3353_ = v___x_3365_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_string_utf8_extract_fast(v_str_3356_, v_startInclusive_3357_, v_endExclusive_3358_);
v___y_3353_ = v___x_3366_;
goto v___jp_3352_;
}
v___jp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3355_ = lean_string_append(v___y_3353_, v___x_3354_);
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3367_);
lean_dec_ref(v_str_3367_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg(){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___closed__0));
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___boxed(lean_object* v___dummy_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg();
return v_res_3374_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg();
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3376_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3378_);
lean_dec_ref(v_s_3378_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3380_, lean_object* v___x_3381_, lean_object* v___x_3382_, lean_object* v_a_3383_, lean_object* v_b_3384_){
_start:
{
lean_object* v_it_3386_; lean_object* v_startInclusive_3387_; lean_object* v_endExclusive_3388_; 
if (lean_obj_tag(v_a_3383_) == 0)
{
lean_object* v_currPos_3392_; lean_object* v_searcher_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3416_; 
v_currPos_3392_ = lean_ctor_get(v_a_3383_, 0);
v_searcher_3393_ = lean_ctor_get(v_a_3383_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3395_ = v_a_3383_;
v_isShared_3396_ = v_isSharedCheck_3416_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_searcher_3393_);
lean_inc(v_currPos_3392_);
lean_dec(v_a_3383_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3416_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v_decide_3397_; 
v_decide_3397_ = lean_nat_dec_eq(v_searcher_3393_, v___x_3382_);
if (v_decide_3397_ == 0)
{
uint32_t v___x_3398_; uint32_t v___x_3399_; uint8_t v___x_3400_; 
v___x_3398_ = 10;
v___x_3399_ = lean_string_utf8_get_fast(v_str_3380_, v_searcher_3393_);
v___x_3400_ = lean_uint32_dec_eq(v___x_3399_, v___x_3398_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3401_ = lean_string_utf8_next_fast(v_str_3380_, v_searcher_3393_);
lean_dec(v_searcher_3393_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v___x_3401_);
v___x_3403_ = v___x_3395_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_currPos_3392_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
v_a_3383_ = v___x_3403_;
goto _start;
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v_slice_3409_; lean_object* v_nextIt_3411_; 
v___x_3406_ = lean_string_utf8_next_fast(v_str_3380_, v_searcher_3393_);
v___x_3407_ = lean_nat_sub(v___x_3406_, v_searcher_3393_);
v___x_3408_ = lean_nat_add(v_searcher_3393_, v___x_3407_);
lean_dec(v___x_3407_);
v_slice_3409_ = l_String_Slice_subslice_x21(v___x_3381_, v_currPos_3392_, v_searcher_3393_);
lean_inc(v___x_3408_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v___x_3408_);
lean_ctor_set(v___x_3395_, 0, v___x_3408_);
v_nextIt_3411_ = v___x_3395_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___x_3408_);
v_nextIt_3411_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v_startInclusive_3412_; lean_object* v_endExclusive_3413_; 
v_startInclusive_3412_ = lean_ctor_get(v_slice_3409_, 0);
lean_inc(v_startInclusive_3412_);
v_endExclusive_3413_ = lean_ctor_get(v_slice_3409_, 1);
lean_inc(v_endExclusive_3413_);
lean_dec_ref(v_slice_3409_);
v_it_3386_ = v_nextIt_3411_;
v_startInclusive_3387_ = v_startInclusive_3412_;
v_endExclusive_3388_ = v_endExclusive_3413_;
goto v___jp_3385_;
}
}
}
else
{
lean_object* v___x_3415_; 
lean_del_object(v___x_3395_);
lean_dec(v_searcher_3393_);
v___x_3415_ = lean_box(1);
lean_inc(v___x_3382_);
v_it_3386_ = v___x_3415_;
v_startInclusive_3387_ = v_currPos_3392_;
v_endExclusive_3388_ = v___x_3382_;
goto v___jp_3385_;
}
}
}
else
{
lean_dec(v___x_3382_);
lean_dec_ref(v_str_3380_);
return v_b_3384_;
}
v___jp_3385_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_inc_ref(v_str_3380_);
v___x_3389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3389_, 0, v_str_3380_);
lean_ctor_set(v___x_3389_, 1, v_startInclusive_3387_);
lean_ctor_set(v___x_3389_, 2, v_endExclusive_3388_);
v___x_3390_ = lean_array_push(v_b_3384_, v___x_3389_);
v_a_3383_ = v_it_3386_;
v_b_3384_ = v___x_3390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v_a_3420_, lean_object* v_b_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3417_, v___x_3418_, v___x_3419_, v_a_3420_, v_b_3421_);
lean_dec_ref(v___x_3418_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3423_, lean_object* v_x_3424_){
_start:
{
if (lean_obj_tag(v_x_3424_) == 0)
{
return v_x_3423_;
}
else
{
lean_object* v_head_3425_; lean_object* v_tail_3426_; lean_object* v___x_3427_; 
v_head_3425_ = lean_ctor_get(v_x_3424_, 0);
v_tail_3426_ = lean_ctor_get(v_x_3424_, 1);
v___x_3427_ = lean_string_append(v_x_3423_, v_head_3425_);
v_x_3423_ = v___x_3427_;
v_x_3424_ = v_tail_3426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3429_, v_x_3430_);
lean_dec(v_x_3430_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3432_, lean_object* v_a_3433_){
_start:
{
if (lean_obj_tag(v_a_3432_) == 0)
{
lean_object* v___x_3434_; 
v___x_3434_ = l_List_reverse___redArg(v_a_3433_);
return v___x_3434_;
}
else
{
lean_object* v_head_3435_; lean_object* v_tail_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_head_3435_ = lean_ctor_get(v_a_3432_, 0);
v_tail_3436_ = lean_ctor_get(v_a_3432_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v_a_3432_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_tail_3436_);
lean_inc(v_head_3435_);
lean_dec(v_a_3432_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3435_);
lean_dec(v_head_3435_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v_a_3433_);
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_a_3433_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v_a_3432_ = v_tail_3436_;
v_a_3433_ = v___x_3442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3450_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_lines_3457_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_string_utf8_byte_size(v_str_3450_);
lean_inc_ref(v_str_3450_);
v___x_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3453_, 0, v_str_3450_);
lean_ctor_set(v___x_3453_, 1, v___x_3451_);
lean_ctor_set(v___x_3453_, 2, v___x_3452_);
v___x_3454_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0);
v___x_3455_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3456_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3450_, v___x_3453_, v___x_3452_, v___x_3454_, v___x_3455_);
lean_dec_ref_known(v___x_3453_, 3);
v_lines_3457_ = lean_array_to_list(v___x_3456_);
if (lean_obj_tag(v_lines_3457_) == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
return v___x_3458_;
}
else
{
lean_object* v_tail_3459_; 
v_tail_3459_ = lean_ctor_get(v_lines_3457_, 1);
if (lean_obj_tag(v_tail_3459_) == 0)
{
lean_object* v_head_3460_; lean_object* v_str_3461_; lean_object* v_startInclusive_3462_; lean_object* v_endExclusive_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_head_3460_ = lean_ctor_get(v_lines_3457_, 0);
lean_inc(v_head_3460_);
lean_dec_ref_known(v_lines_3457_, 2);
v_str_3461_ = lean_ctor_get(v_head_3460_, 0);
lean_inc_ref(v_str_3461_);
v_startInclusive_3462_ = lean_ctor_get(v_head_3460_, 1);
lean_inc(v_startInclusive_3462_);
v_endExclusive_3463_ = lean_ctor_get(v_head_3460_, 2);
lean_inc(v_endExclusive_3463_);
lean_dec(v_head_3460_);
v___x_3464_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3465_ = lean_string_utf8_extract_fast(v_str_3461_, v_startInclusive_3462_, v_endExclusive_3463_);
lean_dec(v_endExclusive_3463_);
lean_dec(v_startInclusive_3462_);
lean_dec_ref(v_str_3461_);
v___x_3466_ = lean_string_append(v___x_3464_, v___x_3465_);
lean_dec_ref(v___x_3465_);
v___x_3467_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3468_ = lean_string_append(v___x_3466_, v___x_3467_);
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_str_3470_; lean_object* v_startInclusive_3471_; lean_object* v_endExclusive_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_inc(v_tail_3459_);
v_head_3469_ = lean_ctor_get(v_lines_3457_, 0);
lean_inc(v_head_3469_);
lean_dec_ref_known(v_lines_3457_, 2);
v_str_3470_ = lean_ctor_get(v_head_3469_, 0);
lean_inc_ref(v_str_3470_);
v_startInclusive_3471_ = lean_ctor_get(v_head_3469_, 1);
lean_inc(v_startInclusive_3471_);
v_endExclusive_3472_ = lean_ctor_get(v_head_3469_, 2);
lean_inc(v_endExclusive_3472_);
lean_dec(v_head_3469_);
v___x_3473_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3474_ = lean_string_utf8_extract_fast(v_str_3470_, v_startInclusive_3471_, v_endExclusive_3472_);
lean_dec(v_endExclusive_3472_);
lean_dec(v_startInclusive_3471_);
lean_dec_ref(v_str_3470_);
v___x_3475_ = lean_string_append(v___x_3473_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3477_ = lean_string_append(v___x_3475_, v___x_3476_);
v___x_3478_ = lean_box(0);
v___x_3479_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3459_, v___x_3478_);
v___x_3480_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3481_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3480_, v___x_3479_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_string_append(v___x_3477_, v___x_3481_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3484_ = lean_string_append(v___x_3482_, v___x_3483_);
return v___x_3484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3485_, lean_object* v___x_3486_, lean_object* v___x_3487_, lean_object* v_inst_3488_, lean_object* v_R_3489_, lean_object* v_a_3490_, lean_object* v_b_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3485_, v___x_3486_, v___x_3487_, v_a_3490_, v_b_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3493_, lean_object* v___x_3494_, lean_object* v___x_3495_, lean_object* v_inst_3496_, lean_object* v_R_3497_, lean_object* v_a_3498_, lean_object* v_b_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3493_, v___x_3494_, v___x_3495_, v_inst_3496_, v_R_3497_, v_a_3498_, v_b_3499_);
lean_dec_ref(v___x_3494_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
if (lean_obj_tag(v_a_3501_) == 0)
{
lean_object* v___x_3503_; 
v___x_3503_ = l_List_reverse___redArg(v_a_3502_);
return v___x_3503_;
}
else
{
lean_object* v_head_3504_; lean_object* v_tail_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3514_; 
v_head_3504_ = lean_ctor_get(v_a_3501_, 0);
v_tail_3505_ = lean_ctor_get(v_a_3501_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3507_ = v_a_3501_;
v_isShared_3508_ = v_isSharedCheck_3514_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_tail_3505_);
lean_inc(v_head_3504_);
lean_dec(v_a_3501_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3514_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3504_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v_a_3502_);
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_a_3502_);
v___x_3511_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
v_a_3501_ = v_tail_3505_;
v_a_3502_ = v___x_3511_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3515_, lean_object* v_pos_3516_){
_start:
{
lean_object* v_str_3517_; lean_object* v_startInclusive_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v_decide_3522_; 
v_str_3517_ = lean_ctor_get(v_s_3515_, 0);
v_startInclusive_3518_ = lean_ctor_get(v_s_3515_, 1);
v___x_3519_ = lean_nat_add(v_startInclusive_3518_, v_pos_3516_);
v___x_3520_ = lean_nat_sub(v___x_3519_, v_startInclusive_3518_);
v___x_3521_ = lean_unsigned_to_nat(0u);
v_decide_3522_ = lean_nat_dec_eq(v___x_3520_, v___x_3521_);
if (v_decide_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3531_; uint32_t v___x_3532_; uint32_t v___x_3533_; uint8_t v___x_3534_; 
lean_inc(v_startInclusive_3518_);
lean_inc_ref(v_str_3517_);
v___x_3523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3523_, 0, v_str_3517_);
lean_ctor_set(v___x_3523_, 1, v_startInclusive_3518_);
lean_ctor_set(v___x_3523_, 2, v___x_3519_);
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_sub(v___x_3520_, v___x_3524_);
lean_dec(v___x_3520_);
v___x_3526_ = l_String_Slice_posLE(v___x_3523_, v___x_3525_);
lean_dec_ref_known(v___x_3523_, 3);
v___x_3531_ = lean_nat_add(v_startInclusive_3518_, v___x_3526_);
v___x_3532_ = lean_string_utf8_get_fast(v_str_3517_, v___x_3531_);
lean_dec(v___x_3531_);
v___x_3533_ = 32;
v___x_3534_ = lean_uint32_dec_eq(v___x_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
uint32_t v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = 9;
v___x_3536_ = lean_uint32_dec_eq(v___x_3532_, v___x_3535_);
if (v___x_3536_ == 0)
{
uint32_t v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = 13;
v___x_3538_ = lean_uint32_dec_eq(v___x_3532_, v___x_3537_);
if (v___x_3538_ == 0)
{
uint32_t v___x_3539_; uint8_t v___x_3540_; 
v___x_3539_ = 10;
v___x_3540_ = lean_uint32_dec_eq(v___x_3532_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_dec(v___x_3526_);
return v_pos_3516_;
}
else
{
goto v___jp_3527_;
}
}
else
{
goto v___jp_3527_;
}
}
else
{
goto v___jp_3527_;
}
}
else
{
goto v___jp_3527_;
}
v___jp_3527_:
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = lean_nat_add(v___x_3526_, v___x_3524_);
v___x_3529_ = lean_nat_dec_le(v___x_3528_, v_pos_3516_);
lean_dec(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_dec(v___x_3526_);
return v_pos_3516_;
}
else
{
lean_dec(v_pos_3516_);
v_pos_3516_ = v___x_3526_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3520_);
lean_dec(v___x_3519_);
return v_pos_3516_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3541_, lean_object* v_pos_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3541_, v_pos_3542_);
lean_dec_ref(v_s_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3545_, lean_object* v_tactic_3546_){
_start:
{
lean_object* v_exts_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v_exts_3547_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3545_, v_tactic_3546_);
v___x_3548_ = lean_array_get_size(v_exts_3547_);
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_nat_dec_eq(v___x_3548_, v___x_3549_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3551_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3552_ = lean_array_to_list(v_exts_3547_);
v___x_3553_ = lean_box(0);
v___x_3554_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3552_, v___x_3553_);
v___x_3555_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3556_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3555_, v___x_3554_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_string_append(v___x_3551_, v___x_3556_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = lean_string_utf8_byte_size(v___x_3557_);
lean_inc_ref(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3549_);
lean_ctor_set(v___x_3559_, 2, v___x_3558_);
v___x_3560_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3559_, v___x_3558_);
lean_dec_ref_known(v___x_3559_, 3);
v___x_3561_ = lean_string_utf8_extract_fast(v___x_3557_, v___x_3549_, v___x_3560_);
lean_dec(v___x_3560_);
lean_dec_ref(v___x_3557_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; 
lean_dec_ref(v_exts_3547_);
v___x_3562_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3563_, lean_object* v_x_3564_){
_start:
{
lean_object* v_fst_3565_; lean_object* v_snd_3566_; lean_object* v___x_3567_; 
v_fst_3565_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_fst_3565_);
v_snd_3566_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_snd_3566_);
lean_dec_ref(v_x_3564_);
v___x_3567_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3565_, v_snd_3566_, v_as_3563_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3568_, lean_object* v_x_3569_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_object* v_k_3570_; lean_object* v_v_3571_; lean_object* v_l_3572_; lean_object* v_r_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_k_3570_ = lean_ctor_get(v_x_3569_, 1);
v_v_3571_ = lean_ctor_get(v_x_3569_, 2);
v_l_3572_ = lean_ctor_get(v_x_3569_, 3);
v_r_3573_ = lean_ctor_get(v_x_3569_, 4);
v___x_3574_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3568_, v_l_3572_);
lean_inc(v_v_3571_);
lean_inc(v_k_3570_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v_k_3570_);
lean_ctor_set(v___x_3575_, 1, v_v_3571_);
v___x_3576_ = lean_array_push(v___x_3574_, v___x_3575_);
v_init_3568_ = v___x_3576_;
v_x_3569_ = v_r_3573_;
goto _start;
}
else
{
return v_init_3568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3578_, v_x_3579_);
lean_dec(v_x_3579_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3581_, lean_object* v_pivot_3582_, lean_object* v_as_3583_, lean_object* v_i_3584_, lean_object* v_k_3585_){
_start:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_nat_dec_lt(v_k_3585_, v_hi_3581_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec(v_k_3585_);
v___x_3587_ = lean_array_fswap(v_as_3583_, v_i_3584_, v_hi_3581_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_i_3584_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; lean_object* v_fst_3590_; lean_object* v_fst_3591_; uint8_t v___x_3592_; 
v___x_3589_ = lean_array_fget_borrowed(v_as_3583_, v_k_3585_);
v_fst_3590_ = lean_ctor_get(v___x_3589_, 0);
v_fst_3591_ = lean_ctor_get(v_pivot_3582_, 0);
v___x_3592_ = l_Lean_Name_quickLt(v_fst_3590_, v_fst_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_unsigned_to_nat(1u);
v___x_3594_ = lean_nat_add(v_k_3585_, v___x_3593_);
lean_dec(v_k_3585_);
v_k_3585_ = v___x_3594_;
goto _start;
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3596_ = lean_array_fswap(v_as_3583_, v_i_3584_, v_k_3585_);
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_nat_add(v_i_3584_, v___x_3597_);
lean_dec(v_i_3584_);
v___x_3599_ = lean_nat_add(v_k_3585_, v___x_3597_);
lean_dec(v_k_3585_);
v_as_3583_ = v___x_3596_;
v_i_3584_ = v___x_3598_;
v_k_3585_ = v___x_3599_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3601_, lean_object* v_pivot_3602_, lean_object* v_as_3603_, lean_object* v_i_3604_, lean_object* v_k_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3601_, v_pivot_3602_, v_as_3603_, v_i_3604_, v_k_3605_);
lean_dec_ref(v_pivot_3602_);
lean_dec(v_hi_3601_);
return v_res_3606_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3607_, lean_object* v_x2_3608_){
_start:
{
lean_object* v_fst_3609_; lean_object* v_fst_3610_; uint8_t v___x_3611_; 
v_fst_3609_ = lean_ctor_get(v_x1_3607_, 0);
v_fst_3610_ = lean_ctor_get(v_x2_3608_, 0);
v___x_3611_ = l_Lean_Name_quickLt(v_fst_3609_, v_fst_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3612_, lean_object* v_x2_3613_){
_start:
{
uint8_t v_res_3614_; lean_object* v_r_3615_; 
v_res_3614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3612_, v_x2_3613_);
lean_dec_ref(v_x2_3613_);
lean_dec_ref(v_x1_3612_);
v_r_3615_ = lean_box(v_res_3614_);
return v_r_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3616_, lean_object* v_as_3617_, lean_object* v_lo_3618_, lean_object* v_hi_3619_){
_start:
{
lean_object* v___y_3621_; uint8_t v___x_3631_; 
v___x_3631_ = lean_nat_dec_lt(v_lo_3618_, v_hi_3619_);
if (v___x_3631_ == 0)
{
lean_dec(v_lo_3618_);
return v_as_3617_;
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_mid_3634_; lean_object* v___y_3636_; lean_object* v___y_3642_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3632_ = lean_nat_add(v_lo_3618_, v_hi_3619_);
v___x_3633_ = lean_unsigned_to_nat(1u);
v_mid_3634_ = lean_nat_shiftr(v___x_3632_, v___x_3633_);
lean_dec(v___x_3632_);
v___x_3647_ = lean_array_fget_borrowed(v_as_3617_, v_mid_3634_);
v___x_3648_ = lean_array_fget_borrowed(v_as_3617_, v_lo_3618_);
v___x_3649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3647_, v___x_3648_);
if (v___x_3649_ == 0)
{
v___y_3642_ = v_as_3617_;
goto v___jp_3641_;
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_array_fswap(v_as_3617_, v_lo_3618_, v_mid_3634_);
v___y_3642_ = v___x_3650_;
goto v___jp_3641_;
}
v___jp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3637_ = lean_array_fget_borrowed(v___y_3636_, v_mid_3634_);
v___x_3638_ = lean_array_fget_borrowed(v___y_3636_, v_hi_3619_);
v___x_3639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_dec(v_mid_3634_);
v___y_3621_ = v___y_3636_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_array_fswap(v___y_3636_, v_mid_3634_, v_hi_3619_);
lean_dec(v_mid_3634_);
v___y_3621_ = v___x_3640_;
goto v___jp_3620_;
}
}
v___jp_3641_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_array_fget_borrowed(v___y_3642_, v_hi_3619_);
v___x_3644_ = lean_array_fget_borrowed(v___y_3642_, v_lo_3618_);
v___x_3645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
v___y_3636_ = v___y_3642_;
goto v___jp_3635_;
}
else
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_array_fswap(v___y_3642_, v_lo_3618_, v_hi_3619_);
v___y_3636_ = v___x_3646_;
goto v___jp_3635_;
}
}
}
v___jp_3620_:
{
lean_object* v_pivot_3622_; lean_object* v___x_3623_; lean_object* v_fst_3624_; lean_object* v_snd_3625_; uint8_t v___x_3626_; 
v_pivot_3622_ = lean_array_fget(v___y_3621_, v_hi_3619_);
lean_inc_n(v_lo_3618_, 2);
v___x_3623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3619_, v_pivot_3622_, v___y_3621_, v_lo_3618_, v_lo_3618_);
lean_dec(v_pivot_3622_);
v_fst_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_fst_3624_);
v_snd_3625_ = lean_ctor_get(v___x_3623_, 1);
lean_inc(v_snd_3625_);
lean_dec_ref(v___x_3623_);
v___x_3626_ = lean_nat_dec_le(v_hi_3619_, v_fst_3624_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3616_, v_snd_3625_, v_lo_3618_, v_fst_3624_);
v___x_3628_ = lean_unsigned_to_nat(1u);
v___x_3629_ = lean_nat_add(v_fst_3624_, v___x_3628_);
lean_dec(v_fst_3624_);
v_as_3617_ = v___x_3627_;
v_lo_3618_ = v___x_3629_;
goto _start;
}
else
{
lean_dec(v_fst_3624_);
lean_dec(v_lo_3618_);
return v_snd_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3651_, lean_object* v_as_3652_, lean_object* v_lo_3653_, lean_object* v_hi_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3651_, v_as_3652_, v_lo_3653_, v_hi_3654_);
lean_dec(v_hi_3654_);
lean_dec(v_n_3651_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3658_, lean_object* v_s_3659_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___y_3665_; lean_object* v___y_3666_; uint8_t v___x_3669_; 
v___x_3660_ = lean_unsigned_to_nat(0u);
v___x_3661_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3662_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3661_, v_s_3659_);
v___x_3663_ = lean_array_get_size(v___x_3662_);
v___x_3669_ = lean_nat_dec_eq(v___x_3663_, v___x_3660_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___y_3673_; uint8_t v___x_3675_; 
v___x_3670_ = lean_unsigned_to_nat(1u);
v___x_3671_ = lean_nat_sub(v___x_3663_, v___x_3670_);
v___x_3675_ = lean_nat_dec_le(v___x_3660_, v___x_3671_);
if (v___x_3675_ == 0)
{
lean_inc(v___x_3671_);
v___y_3673_ = v___x_3671_;
goto v___jp_3672_;
}
else
{
v___y_3673_ = v___x_3660_;
goto v___jp_3672_;
}
v___jp_3672_:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_nat_dec_le(v___y_3673_, v___x_3671_);
if (v___x_3674_ == 0)
{
lean_dec(v___x_3671_);
lean_inc(v___y_3673_);
v___y_3665_ = v___y_3673_;
v___y_3666_ = v___y_3673_;
goto v___jp_3664_;
}
else
{
v___y_3665_ = v___y_3673_;
v___y_3666_ = v___x_3671_;
goto v___jp_3664_;
}
}
}
else
{
lean_object* v___x_3676_; 
lean_inc_ref_n(v___x_3662_, 2);
v___x_3676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3662_);
lean_ctor_set(v___x_3676_, 1, v___x_3662_);
lean_ctor_set(v___x_3676_, 2, v___x_3662_);
return v___x_3676_;
}
v___jp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3663_, v___x_3662_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_inc_ref_n(v___x_3667_, 2);
v___x_3668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
lean_ctor_set(v___x_3668_, 2, v___x_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3677_, lean_object* v_s_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3677_, v_s_3678_);
lean_dec(v_s_3678_);
lean_dec_ref(v_x_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3680_){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3682_, v_es_3680_);
v___x_3684_ = lean_array_get_size(v___x_3683_);
v___x_3685_ = lean_nat_dec_eq(v___x_3684_, v___x_3681_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___y_3689_; uint8_t v___x_3693_; 
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_nat_sub(v___x_3684_, v___x_3686_);
v___x_3693_ = lean_nat_dec_le(v___x_3681_, v___x_3687_);
if (v___x_3693_ == 0)
{
lean_inc(v___x_3687_);
v___y_3689_ = v___x_3687_;
goto v___jp_3688_;
}
else
{
v___y_3689_ = v___x_3681_;
goto v___jp_3688_;
}
v___jp_3688_:
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_nat_dec_le(v___y_3689_, v___x_3687_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; 
lean_dec(v___x_3687_);
lean_inc(v___y_3689_);
v___x_3691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3684_, v___x_3683_, v___y_3689_, v___y_3689_);
lean_dec(v___y_3689_);
return v___x_3691_;
}
else
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3684_, v___x_3683_, v___y_3689_, v___x_3687_);
lean_dec(v___x_3687_);
return v___x_3692_;
}
}
}
else
{
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_3694_);
lean_dec(v_es_3694_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_3696_, lean_object* v_x_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3696_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_3701_, v_x_3702_, v___y_3703_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v_x_3702_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3733_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_3736_, lean_object* v_t_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3736_, v_t_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3739_, lean_object* v_t_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_3739_, v_t_3740_);
lean_dec(v_t_3740_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_3742_, lean_object* v_as_3743_, lean_object* v_lo_3744_, lean_object* v_hi_3745_, lean_object* v_w_3746_, lean_object* v_hlo_3747_, lean_object* v_hhi_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3742_, v_as_3743_, v_lo_3744_, v_hi_3745_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3750_, lean_object* v_as_3751_, lean_object* v_lo_3752_, lean_object* v_hi_3753_, lean_object* v_w_3754_, lean_object* v_hlo_3755_, lean_object* v_hhi_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_3750_, v_as_3751_, v_lo_3752_, v_hi_3753_, v_w_3754_, v_hlo_3755_, v_hhi_3756_);
lean_dec(v_hi_3753_);
lean_dec(v_n_3750_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3758_, lean_object* v_lo_3759_, lean_object* v_hi_3760_, lean_object* v_hhi_3761_, lean_object* v_pivot_3762_, lean_object* v_as_3763_, lean_object* v_i_3764_, lean_object* v_k_3765_, lean_object* v_ilo_3766_, lean_object* v_ik_3767_, lean_object* v_w_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3760_, v_pivot_3762_, v_as_3763_, v_i_3764_, v_k_3765_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3770_, lean_object* v_lo_3771_, lean_object* v_hi_3772_, lean_object* v_hhi_3773_, lean_object* v_pivot_3774_, lean_object* v_as_3775_, lean_object* v_i_3776_, lean_object* v_k_3777_, lean_object* v_ilo_3778_, lean_object* v_ik_3779_, lean_object* v_w_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(v_n_3770_, v_lo_3771_, v_hi_3772_, v_hhi_3773_, v_pivot_3774_, v_as_3775_, v_i_3776_, v_k_3777_, v_ilo_3778_, v_ik_3779_, v_w_3780_);
lean_dec_ref(v_pivot_3774_);
lean_dec(v_hi_3772_);
lean_dec(v_lo_3771_);
lean_dec(v_n_3770_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_3783_, lean_object* v___x_3784_, lean_object* v_toPure_3785_, lean_object* v___f_3786_, lean_object* v_env_3787_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3787_, v_tac_3783_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v___x_3792_; lean_object* v_toEnvExtension_3793_; lean_object* v_asyncMode_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec_ref(v___f_3786_);
v___x_3792_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3793_ = lean_ctor_get(v___x_3792_, 0);
v_asyncMode_3794_ = lean_ctor_get(v_toEnvExtension_3793_, 2);
v___x_3795_ = lean_box(0);
v___x_3796_ = 0;
v___x_3797_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3784_, v___x_3792_, v_env_3787_, v_asyncMode_3794_, v___x_3795_, v___x_3796_);
v___x_3798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3797_, v_tac_3783_);
lean_dec(v_tac_3783_);
lean_dec(v___x_3797_);
v___x_3799_ = lean_apply_2(v_toPure_3785_, lean_box(0), v___x_3798_);
return v___x_3799_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v_val_3800_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3801_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3802_ = 0;
v___x_3803_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3784_, v___x_3801_, v_env_3787_, v_val_3800_, v___x_3802_);
lean_dec(v_val_3800_);
lean_dec_ref(v_env_3787_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v___x_3805_ = lean_array_get_size(v___x_3803_);
v___x_3806_ = lean_nat_dec_lt(v___x_3804_, v___x_3805_);
if (v___x_3806_ == 0)
{
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___f_3786_);
lean_dec(v_tac_3783_);
goto v___jp_3788_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = lean_nat_sub(v___x_3805_, v___x_3807_);
v___x_3809_ = lean_nat_dec_le(v___x_3804_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_dec(v___x_3808_);
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___f_3786_);
lean_dec(v_tac_3783_);
goto v___jp_3788_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_tac_3783_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_3813_ = l_Array_binSearchAux___redArg(v___f_3786_, v___x_3812_, v___x_3803_, v___x_3811_, v___x_3804_, v___x_3808_);
lean_dec_ref(v___x_3803_);
if (lean_obj_tag(v___x_3813_) == 0)
{
goto v___jp_3788_;
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
v_val_3814_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3816_ = v___x_3813_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_val_3814_);
lean_dec(v___x_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v_snd_3818_; lean_object* v___x_3820_; 
v_snd_3818_ = lean_ctor_get(v_val_3814_, 1);
lean_inc(v_snd_3818_);
lean_dec(v_val_3814_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v_snd_3818_);
v___x_3820_ = v___x_3816_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_snd_3818_);
v___x_3820_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_apply_2(v_toPure_3785_, lean_box(0), v___x_3820_);
return v___x_3821_;
}
}
}
}
}
}
v___jp_3788_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_box(0);
v___x_3790_ = lean_apply_2(v_toPure_3785_, lean_box(0), v___x_3789_);
return v___x_3790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_3825_, lean_object* v_inst_3826_, lean_object* v_tac_3827_){
_start:
{
lean_object* v_toApplicative_3828_; lean_object* v_toBind_3829_; lean_object* v_getEnv_3830_; lean_object* v_toPure_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; lean_object* v___f_3834_; lean_object* v___x_3835_; 
v_toApplicative_3828_ = lean_ctor_get(v_inst_3825_, 0);
lean_inc_ref(v_toApplicative_3828_);
v_toBind_3829_ = lean_ctor_get(v_inst_3825_, 1);
lean_inc(v_toBind_3829_);
lean_dec_ref(v_inst_3825_);
v_getEnv_3830_ = lean_ctor_get(v_inst_3826_, 0);
lean_inc(v_getEnv_3830_);
lean_dec_ref(v_inst_3826_);
v_toPure_3831_ = lean_ctor_get(v_toApplicative_3828_, 1);
lean_inc(v_toPure_3831_);
lean_dec_ref(v_toApplicative_3828_);
v___f_3832_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0));
v___x_3833_ = lean_box(1);
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3834_, 0, v_tac_3827_);
lean_closure_set(v___f_3834_, 1, v___x_3833_);
lean_closure_set(v___f_3834_, 2, v_toPure_3831_);
lean_closure_set(v___f_3834_, 3, v___f_3832_);
v___x_3835_ = lean_apply_4(v_toBind_3829_, lean_box(0), lean_box(0), v_getEnv_3830_, v___f_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_3836_, lean_object* v_inst_3837_, lean_object* v_inst_3838_, lean_object* v_tac_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_3837_, v_inst_3838_, v_tac_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v_addEntryFn_3841_, lean_object* v___x_3842_, lean_object* v_s_3843_){
_start:
{
lean_object* v_importedEntries_3844_; lean_object* v_state_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
v_importedEntries_3844_ = lean_ctor_get(v_s_3843_, 0);
v_state_3845_ = lean_ctor_get(v_s_3843_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_s_3843_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3847_ = v_s_3843_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_state_3845_);
lean_inc(v_importedEntries_3844_);
lean_dec(v_s_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_state_3849_; lean_object* v___x_3851_; 
v_state_3849_ = lean_apply_2(v_addEntryFn_3841_, v_state_3845_, v___x_3842_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 1, v_state_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_importedEntries_3844_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_state_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_3854_, lean_object* v_k_3855_, lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_m_3860_; lean_object* v_a_3861_; uint8_t v___x_3862_; 
v___x_3858_ = lean_nat_add(v_x_3856_, v_x_3857_);
v___x_3859_ = lean_unsigned_to_nat(1u);
v_m_3860_ = lean_nat_shiftr(v___x_3858_, v___x_3859_);
lean_dec(v___x_3858_);
v_a_3861_ = lean_array_fget_borrowed(v_as_3854_, v_m_3860_);
v___x_3862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3861_, v_k_3855_);
if (v___x_3862_ == 0)
{
uint8_t v___x_3863_; 
lean_dec(v_x_3857_);
v___x_3863_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3855_, v_a_3861_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; 
lean_dec(v_m_3860_);
lean_dec(v_x_3856_);
lean_inc(v_a_3861_);
v___x_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3864_, 0, v_a_3861_);
return v___x_3864_;
}
else
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = lean_nat_dec_eq(v_m_3860_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3867_ = lean_nat_sub(v_m_3860_, v___x_3859_);
lean_dec(v_m_3860_);
v___x_3868_ = lean_nat_dec_lt(v___x_3867_, v_x_3856_);
if (v___x_3868_ == 0)
{
v_x_3857_ = v___x_3867_;
goto _start;
}
else
{
lean_object* v___x_3870_; 
lean_dec(v___x_3867_);
lean_dec(v_x_3856_);
v___x_3870_ = lean_box(0);
return v___x_3870_;
}
}
else
{
lean_object* v___x_3871_; 
lean_dec(v_m_3860_);
lean_dec(v_x_3856_);
v___x_3871_ = lean_box(0);
return v___x_3871_;
}
}
}
else
{
lean_object* v___x_3872_; uint8_t v___x_3873_; 
lean_dec(v_x_3856_);
v___x_3872_ = lean_nat_add(v_m_3860_, v___x_3859_);
lean_dec(v_m_3860_);
v___x_3873_ = lean_nat_dec_le(v___x_3872_, v_x_3857_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; 
lean_dec(v___x_3872_);
lean_dec(v_x_3857_);
v___x_3874_ = lean_box(0);
return v___x_3874_;
}
else
{
v_x_3856_ = v___x_3872_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_3876_, lean_object* v_k_3877_, lean_object* v_x_3878_, lean_object* v_x_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3876_, v_k_3877_, v_x_3878_, v_x_3879_);
lean_dec_ref(v_k_3877_);
lean_dec_ref(v_as_3876_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v_env_3889_; lean_object* v___x_3890_; 
v___x_3884_ = lean_box(1);
v___x_3885_ = lean_st_ref_get(v___y_3882_);
v_env_3889_ = lean_ctor_get(v___x_3885_, 0);
lean_inc_ref(v_env_3889_);
lean_dec(v___x_3885_);
v___x_3890_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3889_, v_tac_3881_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v___x_3891_; lean_object* v_toEnvExtension_3892_; lean_object* v_asyncMode_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3891_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3892_ = lean_ctor_get(v___x_3891_, 0);
v_asyncMode_3893_ = lean_ctor_get(v_toEnvExtension_3892_, 2);
v___x_3894_ = lean_box(0);
v___x_3895_ = 0;
v___x_3896_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3884_, v___x_3891_, v_env_3889_, v_asyncMode_3893_, v___x_3894_, v___x_3895_);
v___x_3897_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3896_, v_tac_3881_);
lean_dec(v_tac_3881_);
lean_dec(v___x_3896_);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3927_; 
v_val_3899_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3901_ = v___x_3890_;
v_isShared_3902_ = v_isSharedCheck_3927_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v___x_3890_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3927_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3903_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3904_ = 0;
v___x_3905_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3884_, v___x_3903_, v_env_3889_, v_val_3899_, v___x_3904_);
lean_dec(v_val_3899_);
lean_dec_ref(v_env_3889_);
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_array_get_size(v___x_3905_);
v___x_3908_ = lean_nat_dec_lt(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_dec_ref(v___x_3905_);
lean_del_object(v___x_3901_);
lean_dec(v_tac_3881_);
goto v___jp_3886_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_sub(v___x_3907_, v___x_3909_);
v___x_3911_ = lean_nat_dec_le(v___x_3906_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_dec(v___x_3910_);
lean_dec_ref(v___x_3905_);
lean_del_object(v___x_3901_);
lean_dec(v_tac_3881_);
goto v___jp_3886_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3912_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v_tac_3881_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_3905_, v___x_3913_, v___x_3906_, v___x_3910_);
lean_dec_ref_known(v___x_3913_, 2);
lean_dec_ref(v___x_3905_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_del_object(v___x_3901_);
goto v___jp_3886_;
}
else
{
lean_object* v_val_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3926_; 
v_val_3915_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3917_ = v___x_3914_;
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_val_3915_);
lean_dec(v___x_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v_snd_3919_; lean_object* v___x_3921_; 
v_snd_3919_ = lean_ctor_get(v_val_3915_, 1);
lean_inc(v_snd_3919_);
lean_dec(v_val_3915_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v_snd_3919_);
v___x_3921_ = v___x_3917_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_snd_3919_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3921_);
v___x_3923_ = v___x_3901_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
}
}
v___jp_3886_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_box(0);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_3928_, v___y_3929_);
lean_dec(v___y_3929_);
return v_res_3931_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3934_ = l_Lean_stringToMessageData(v___x_3933_);
return v___x_3934_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3937_ = l_Lean_stringToMessageData(v___x_3936_);
return v___x_3937_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
return v___x_3940_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
return v___x_3943_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_3953_, lean_object* v___x_3954_, lean_object* v___x_3955_, lean_object* v___x_3956_, lean_object* v_name_3957_, lean_object* v_decl_3958_, lean_object* v_stx_3959_, uint8_t v_kind_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_nextMacroScope_3965_; lean_object* v_ngen_3966_; lean_object* v_auxDeclNGen_3967_; lean_object* v_traceState_3968_; lean_object* v_recordedDeps_3969_; lean_object* v_messages_3970_; lean_object* v_infoState_3971_; lean_object* v_snapshotTasks_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v_name_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; uint8_t v___x_4130_; uint8_t v___x_4131_; 
v___x_4130_ = 0;
v___x_4131_ = l_Lean_instBEqAttributeKind_beq(v_kind_3960_, v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
lean_dec(v_stx_3959_);
lean_dec(v_decl_3958_);
lean_dec_ref(v___x_3956_);
lean_dec_ref(v___x_3955_);
lean_dec_ref(v___x_3954_);
lean_dec(v___x_3953_);
v___x_4132_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_3957_, v_kind_3960_, v___y_3961_, v___y_3962_);
return v___x_4132_;
}
else
{
goto v___jp_4089_;
}
v___jp_3964_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3976_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_3977_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3977_, 0, v___y_3975_);
lean_ctor_set(v___x_3977_, 1, v_nextMacroScope_3965_);
lean_ctor_set(v___x_3977_, 2, v_ngen_3966_);
lean_ctor_set(v___x_3977_, 3, v_auxDeclNGen_3967_);
lean_ctor_set(v___x_3977_, 4, v_traceState_3968_);
lean_ctor_set(v___x_3977_, 5, v___x_3976_);
lean_ctor_set(v___x_3977_, 6, v_recordedDeps_3969_);
lean_ctor_set(v___x_3977_, 7, v_messages_3970_);
lean_ctor_set(v___x_3977_, 8, v_infoState_3971_);
lean_ctor_set(v___x_3977_, 9, v_snapshotTasks_3972_);
v___x_3978_ = lean_st_ref_put(v___y_3974_, v___x_3977_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___y_3973_);
return v___x_3979_;
}
v___jp_3980_:
{
lean_object* v___x_3983_; lean_object* v_env_3984_; lean_object* v_nextMacroScope_3985_; lean_object* v_ngen_3986_; lean_object* v_auxDeclNGen_3987_; lean_object* v_traceState_3988_; lean_object* v_recordedDeps_3989_; lean_object* v_messages_3990_; lean_object* v_infoState_3991_; lean_object* v_snapshotTasks_3992_; lean_object* v___x_3993_; lean_object* v_toEnvExtension_3994_; lean_object* v_addEntryFn_3995_; lean_object* v_asyncMode_3996_; uint8_t v_logWrites_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___f_4000_; uint8_t v___x_4001_; 
v___x_3983_ = lean_st_ref_take(v___y_3982_);
v_env_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc_ref(v_env_3984_);
v_nextMacroScope_3985_ = lean_ctor_get(v___x_3983_, 1);
lean_inc(v_nextMacroScope_3985_);
v_ngen_3986_ = lean_ctor_get(v___x_3983_, 2);
lean_inc_ref(v_ngen_3986_);
v_auxDeclNGen_3987_ = lean_ctor_get(v___x_3983_, 3);
lean_inc_ref(v_auxDeclNGen_3987_);
v_traceState_3988_ = lean_ctor_get(v___x_3983_, 4);
lean_inc_ref(v_traceState_3988_);
v_recordedDeps_3989_ = lean_ctor_get(v___x_3983_, 6);
lean_inc_ref(v_recordedDeps_3989_);
v_messages_3990_ = lean_ctor_get(v___x_3983_, 7);
lean_inc_ref(v_messages_3990_);
v_infoState_3991_ = lean_ctor_get(v___x_3983_, 8);
lean_inc_ref(v_infoState_3991_);
v_snapshotTasks_3992_ = lean_ctor_get(v___x_3983_, 9);
lean_inc_ref(v_snapshotTasks_3992_);
lean_dec(v___x_3983_);
v___x_3993_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3994_ = lean_ctor_get(v___x_3993_, 0);
v_addEntryFn_3995_ = lean_ctor_get(v___x_3993_, 3);
v_asyncMode_3996_ = lean_ctor_get(v_toEnvExtension_3994_, 2);
v_logWrites_3997_ = lean_ctor_get_uint8(v_toEnvExtension_3994_, sizeof(void*)*6);
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v_decl_3958_);
lean_ctor_set(v___x_3999_, 1, v___y_3981_);
lean_inc(v_addEntryFn_3995_);
v___f_4000_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_4000_, 0, v_addEntryFn_3995_);
lean_closure_set(v___f_4000_, 1, v___x_3999_);
v___x_4001_ = 1;
if (v_logWrites_3997_ == 0)
{
lean_object* v___x_4002_; 
lean_inc_ref(v_toEnvExtension_3994_);
v___x_4002_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3994_, v_env_3984_, v___f_4000_, v_asyncMode_3996_, v___x_3953_, v___x_4001_);
v_nextMacroScope_3965_ = v_nextMacroScope_3985_;
v_ngen_3966_ = v_ngen_3986_;
v_auxDeclNGen_3967_ = v_auxDeclNGen_3987_;
v_traceState_3968_ = v_traceState_3988_;
v_recordedDeps_3969_ = v_recordedDeps_3989_;
v_messages_3970_ = v_messages_3990_;
v_infoState_3971_ = v_infoState_3991_;
v_snapshotTasks_3972_ = v_snapshotTasks_3992_;
v___y_3973_ = v___x_3998_;
v___y_3974_ = v___y_3982_;
v___y_3975_ = v___x_4002_;
goto v___jp_3964_;
}
else
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_inc_ref_n(v_toEnvExtension_3994_, 2);
v___x_4003_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3994_, v_env_3984_);
lean_dec_ref(v_env_3984_);
v___x_4004_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3994_, v___x_4003_, v___f_4000_, v_asyncMode_3996_, v___x_3953_, v___x_4001_);
v_nextMacroScope_3965_ = v_nextMacroScope_3985_;
v_ngen_3966_ = v_ngen_3986_;
v_auxDeclNGen_3967_ = v_auxDeclNGen_3987_;
v_traceState_3968_ = v_traceState_3988_;
v_recordedDeps_3969_ = v_recordedDeps_3989_;
v_messages_3970_ = v_messages_3990_;
v_infoState_3971_ = v_infoState_3991_;
v_snapshotTasks_3972_ = v_snapshotTasks_3992_;
v___y_3973_ = v___x_3998_;
v___y_3974_ = v___y_3982_;
v___y_3975_ = v___x_4004_;
goto v___jp_3964_;
}
}
v___jp_4005_:
{
lean_object* v___x_4009_; lean_object* v_a_4010_; 
lean_inc(v_decl_3958_);
v___x_4009_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_3958_, v___y_4008_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
if (lean_obj_tag(v_a_4010_) == 1)
{
lean_object* v_val_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec_ref(v___y_4006_);
lean_dec(v___x_3953_);
v_val_4011_ = lean_ctor_get(v_a_4010_, 0);
lean_inc(v_val_4011_);
lean_dec_ref_known(v_a_4010_, 1);
v___x_4012_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4013_ = 0;
v___x_4014_ = l_Lean_MessageData_ofConstName(v_decl_3958_, v___x_4013_);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4012_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = l_Lean_stringToMessageData(v_val_4011_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4017_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4021_, v___y_4007_, v___y_4008_);
return v___x_4022_;
}
else
{
lean_dec(v_a_4010_);
v___y_3981_ = v___y_4006_;
v___y_3982_ = v___y_4008_;
goto v___jp_3980_;
}
}
v___jp_4023_:
{
lean_object* v___x_4027_; lean_object* v_env_4028_; lean_object* v___x_4029_; 
v___x_4027_ = lean_st_ref_get(v___y_4026_);
v_env_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc_ref(v_env_4028_);
lean_dec(v___x_4027_);
lean_inc(v_decl_3958_);
v___x_4029_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4028_, v_decl_3958_);
if (lean_obj_tag(v___x_4029_) == 1)
{
lean_object* v_val_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec_ref(v___y_4024_);
lean_dec(v___x_3953_);
v_val_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4032_ = 0;
v___x_4033_ = l_Lean_MessageData_ofConstName(v_decl_3958_, v___x_4032_);
v___x_4034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4031_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_4036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v___x_4037_ = l_Lean_MessageData_ofConstName(v_val_4030_, v___x_4032_);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v___x_4031_);
v___x_4040_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3959_, v___x_4039_, v___y_4025_, v___y_4026_);
lean_dec(v_stx_3959_);
return v___x_4040_;
}
else
{
lean_dec(v___x_4029_);
lean_dec(v_stx_3959_);
v___y_4006_ = v___y_4024_;
v___y_4007_ = v___y_4025_;
v___y_4008_ = v___y_4026_;
goto v___jp_4005_;
}
}
v___jp_4041_:
{
lean_object* v___x_4046_; lean_object* v_env_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_st_ref_get(v___y_4045_);
v_env_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc_ref(v_env_4047_);
lean_dec(v___x_4046_);
v___x_4048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4047_, v_decl_3958_);
lean_dec_ref(v_env_4047_);
if (lean_obj_tag(v___x_4048_) == 1)
{
lean_object* v_val_4049_; lean_object* v___x_4050_; lean_object* v_env_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
lean_dec_ref(v___y_4042_);
lean_dec(v___x_3953_);
v_val_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_val_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = lean_st_ref_get(v___y_4045_);
v_env_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc_ref(v_env_4051_);
lean_dec(v___x_4050_);
v___x_4052_ = l_Lean_Environment_allImportedModuleNames(v_env_4051_);
lean_dec_ref(v_env_4051_);
v___x_4053_ = lean_array_get_size(v___x_4052_);
v___x_4054_ = lean_nat_dec_lt(v_val_4049_, v___x_4053_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec_ref(v___x_4052_);
lean_dec(v_val_4049_);
v___x_4055_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4056_ = l_Lean_MessageData_ofConstName(v_decl_3958_, v___y_4043_);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3959_, v___x_4059_, v___y_4044_, v___y_4045_);
lean_dec(v_stx_3959_);
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4061_ = lean_array_fget(v___x_4052_, v_val_4049_);
lean_dec(v_val_4049_);
lean_dec_ref(v___x_4052_);
v___x_4062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4063_ = l_Lean_MessageData_ofConstName(v_decl_3958_, v___y_4043_);
v___x_4064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4064_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
v___x_4067_ = l_Lean_MessageData_ofName(v___x_4061_);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3959_, v___x_4070_, v___y_4044_, v___y_4045_);
lean_dec(v_stx_3959_);
return v___x_4071_;
}
}
else
{
lean_dec(v___x_4048_);
v___y_4024_ = v___y_4042_;
v___y_4025_ = v___y_4044_;
v___y_4026_ = v___y_4045_;
goto v___jp_4023_;
}
}
v___jp_4072_:
{
lean_object* v___x_4076_; lean_object* v_env_4077_; uint8_t v___x_4078_; lean_object* v___x_4079_; 
v___x_4076_ = lean_st_ref_get(v___y_4075_);
v_env_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc_ref(v_env_4077_);
lean_dec(v___x_4076_);
v___x_4078_ = 0;
lean_inc(v_decl_3958_);
v___x_4079_ = l_Lean_Environment_find_x3f(v_env_4077_, v_decl_3958_, v___x_4078_);
if (lean_obj_tag(v___x_4079_) == 0)
{
v___y_4024_ = v_name_4073_;
v___y_4025_ = v___y_4074_;
v___y_4026_ = v___y_4075_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4080_; lean_object* v_env_4081_; uint8_t v___x_4082_; 
lean_dec_ref_known(v___x_4079_, 1);
v___x_4080_ = lean_st_ref_get(v___y_4075_);
v_env_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4080_);
v___x_4082_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4081_, v_decl_3958_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_dec_ref(v_name_4073_);
lean_dec(v___x_3953_);
v___x_4083_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4084_ = l_Lean_MessageData_ofConstName(v_decl_3958_, v___x_4078_);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4085_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3959_, v___x_4087_, v___y_4074_, v___y_4075_);
lean_dec(v_stx_3959_);
return v___x_4088_;
}
else
{
v___y_4042_ = v_name_4073_;
v___y_4043_ = v___x_4078_;
v___y_4044_ = v___y_4074_;
v___y_4045_ = v___y_4075_;
goto v___jp_4041_;
}
}
}
v___jp_4089_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4090_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4091_ = l_Lean_Name_mkStr4(v___x_3954_, v___x_3955_, v___x_4090_, v___x_3956_);
lean_inc(v_stx_3959_);
v___x_4092_ = l_Lean_Syntax_isOfKind(v_stx_3959_, v___x_4091_);
lean_dec(v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_stx_3959_);
lean_dec(v_decl_3958_);
lean_dec(v___x_3953_);
v___x_4093_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4094_ = l_Lean_MessageData_ofName(v_name_3957_);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4097_, v___y_3961_, v___y_3962_);
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
else
{
lean_object* v___x_4107_; lean_object* v_name_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4107_ = lean_unsigned_to_nat(1u);
v_name_4108_ = l_Lean_Syntax_getArg(v_stx_3959_, v___x_4107_);
v___x_4109_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4108_);
v___x_4110_ = l_Lean_Syntax_isOfKind(v_name_4108_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4111_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4108_);
v___x_4112_ = l_Lean_Syntax_isOfKind(v_name_4108_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v_name_4108_);
lean_dec(v_stx_3959_);
lean_dec(v_decl_3958_);
lean_dec(v___x_3953_);
v___x_4113_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4114_ = l_Lean_MessageData_ofName(v_name_3957_);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4113_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4117_, v___y_3961_, v___y_3962_);
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
else
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v_name_3957_);
v___x_4127_ = l_Lean_TSyntax_getId(v_name_4108_);
lean_dec(v_name_4108_);
v___x_4128_ = l_Lean_Name_toString(v___x_4127_, v___x_4110_);
v_name_4073_ = v___x_4128_;
v___y_4074_ = v___y_3961_;
v___y_4075_ = v___y_3962_;
goto v___jp_4072_;
}
}
else
{
lean_object* v___x_4129_; 
lean_dec(v_name_3957_);
v___x_4129_ = l_Lean_TSyntax_getString(v_name_4108_);
lean_dec(v_name_4108_);
v_name_4073_ = v___x_4129_;
v___y_4074_ = v___y_3961_;
v___y_4075_ = v___y_3962_;
goto v___jp_4072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v___x_4133_, lean_object* v___x_4134_, lean_object* v___x_4135_, lean_object* v___x_4136_, lean_object* v_name_4137_, lean_object* v_decl_4138_, lean_object* v_stx_4139_, lean_object* v_kind_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
uint8_t v_kind_boxed_4144_; lean_object* v_res_4145_; 
v_kind_boxed_4144_ = lean_unbox(v_kind_4140_);
v_res_4145_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(v___x_4133_, v___x_4134_, v___x_4135_, v___x_4136_, v_name_4137_, v_decl_4138_, v_stx_4139_, v_kind_boxed_4144_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4145_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_unsigned_to_nat(3374007381u);
v___x_4158_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4159_ = l_Lean_Name_num___override(v___x_4158_, v___x_4157_);
return v___x_4159_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4160_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4161_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4162_ = l_Lean_Name_str___override(v___x_4161_, v___x_4160_);
return v___x_4162_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4164_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4165_ = l_Lean_Name_str___override(v___x_4164_, v___x_4163_);
return v___x_4165_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_unsigned_to_nat(2u);
v___x_4167_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4168_ = l_Lean_Name_num___override(v___x_4167_, v___x_4166_);
return v___x_4168_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v_name_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4170_ = 2;
v___x_4171_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v_name_4172_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4173_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4174_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v_name_4172_);
lean_ctor_set(v___x_4174_, 2, v___x_4171_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*3, v___x_4170_);
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4175_; lean_object* v___f_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___f_4175_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___f_4176_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4177_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v___f_4176_);
lean_ctor_set(v___x_4178_, 2, v___f_4175_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4181_ = l_Lean_registerBuiltinAttribute(v___x_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object* v_tac_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4184_, v___y_4186_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tac_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(v_tac_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4194_, lean_object* v_k_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_, lean_object* v_x_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4194_, v_k_4195_, v_x_4196_, v_x_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4200_, lean_object* v_k_4201_, lean_object* v_x_4202_, lean_object* v_x_4203_, lean_object* v_x_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(v_as_4200_, v_k_4201_, v_x_4202_, v_x_4203_, v_x_4204_);
lean_dec_ref(v_k_4201_);
lean_dec_ref(v_as_4200_);
return v_res_4205_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0));
v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object* v___x_4209_, lean_object* v___x_4210_, lean_object* v_catName_4211_, lean_object* v_declName_4212_, uint8_t v___builtIn_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; uint8_t v___x_4218_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4243_; lean_object* v___y_4244_; 
v___x_4217_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_4218_ = lean_name_eq(v_catName_4211_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4260_; lean_object* v_env_4261_; lean_object* v___x_4262_; 
v___x_4260_ = lean_st_ref_get(v___y_4215_);
v_env_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc_ref(v_env_4261_);
lean_dec(v___x_4260_);
lean_inc(v_declName_4212_);
v___x_4262_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4261_, v_declName_4212_);
if (lean_obj_tag(v___x_4262_) == 0)
{
v___y_4243_ = v___y_4214_;
v___y_4244_ = v___y_4215_;
goto v___jp_4242_;
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_dec_ref_known(v___x_4262_, 1);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
v___x_4263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4264_ = l_Lean_MessageData_ofConstName(v_declName_4212_, v___x_4218_);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4267_, v___y_4214_, v___y_4215_);
return v___x_4268_;
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec(v_declName_4212_);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
v___x_4269_ = lean_box(0);
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
v___jp_4219_:
{
lean_object* v___x_4222_; lean_object* v_env_4223_; lean_object* v___x_4224_; lean_object* v_toEnvExtension_4225_; lean_object* v_asyncMode_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4222_ = lean_st_ref_get(v___y_4221_);
v_env_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc_ref(v_env_4223_);
lean_dec(v___x_4222_);
v___x_4224_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4225_ = lean_ctor_get(v___x_4224_, 0);
v_asyncMode_4226_ = lean_ctor_get(v_toEnvExtension_4225_, 2);
v___x_4227_ = lean_box(0);
v___x_4228_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4209_, v___x_4224_, v_env_4223_, v_asyncMode_4226_, v___x_4227_, v___x_4218_);
v___x_4229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4228_, v_declName_4212_);
lean_dec(v___x_4228_);
if (lean_obj_tag(v___x_4229_) == 1)
{
lean_object* v_val_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_val_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_val_4230_);
lean_dec_ref_known(v___x_4229_, 1);
v___x_4231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4232_ = l_Lean_MessageData_ofConstName(v_declName_4212_, v___x_4218_);
v___x_4233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4231_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
v___x_4234_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1);
v___x_4235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4233_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = l_Lean_stringToMessageData(v_val_4230_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4235_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
lean_ctor_set(v___x_4238_, 1, v___x_4231_);
v___x_4239_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4238_, v___y_4220_, v___y_4221_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec(v___x_4229_);
lean_dec(v_declName_4212_);
v___x_4240_ = lean_box(0);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
return v___x_4241_;
}
}
v___jp_4242_:
{
lean_object* v___x_4245_; lean_object* v_env_4246_; lean_object* v___x_4247_; lean_object* v_toEnvExtension_4248_; lean_object* v_asyncMode_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4245_ = lean_st_ref_get(v___y_4244_);
v_env_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc_ref(v_env_4246_);
lean_dec(v___x_4245_);
v___x_4247_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4248_ = lean_ctor_get(v___x_4247_, 0);
v_asyncMode_4249_ = lean_ctor_get(v_toEnvExtension_4248_, 2);
v___x_4250_ = lean_box(0);
v___x_4251_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4210_, v___x_4247_, v_env_4246_, v_asyncMode_4249_, v___x_4250_, v___x_4218_);
v___x_4252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4251_, v_declName_4212_);
lean_dec(v___x_4251_);
if (lean_obj_tag(v___x_4252_) == 1)
{
lean_object* v_val_4253_; 
v_val_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_val_4253_);
lean_dec_ref_known(v___x_4252_, 1);
if (lean_obj_tag(v_val_4253_) == 0)
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_dec_ref_known(v_val_4253_, 5);
lean_dec(v___x_4209_);
v___x_4254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4255_ = l_Lean_MessageData_ofConstName(v_declName_4212_, v___x_4218_);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4258_, v___y_4243_, v___y_4244_);
return v___x_4259_;
}
else
{
v___y_4220_ = v___y_4243_;
v___y_4221_ = v___y_4244_;
goto v___jp_4219_;
}
}
else
{
lean_dec(v___x_4252_);
v___y_4220_ = v___y_4243_;
v___y_4221_ = v___y_4244_;
goto v___jp_4219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v_catName_4273_, lean_object* v_declName_4274_, lean_object* v___builtIn_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
uint8_t v___builtIn_boxed_4279_; lean_object* v_res_4280_; 
v___builtIn_boxed_4279_ = lean_unbox(v___builtIn_4275_);
v_res_4280_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(v___x_4271_, v___x_4272_, v_catName_4273_, v_declName_4274_, v___builtIn_boxed_4279_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v_catName_4273_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics));
v___x_4286_ = l_Lean_Parser_registerParserAttributeHook(v___x_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object* v_a_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
return v_res_4288_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Tactic_Doc_tacticAlternativeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Tactic_Doc_tacticAlternativeExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Tactic_Doc_knownTacticTagExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Tactic_Doc_knownTacticTagExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Tactic_Doc_tacticTagExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Tactic_Doc_tacticTagExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Tactic_Doc_tacticDocExtExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Tactic_Doc_tacticDocExtExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_Tactic_Doc_tacticNameExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_Tactic_Doc_tacticNameExt);
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Attr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_Parser_Attr(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
