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
uint8_t v___x_8627__boxed_783_; size_t v_i_boxed_784_; size_t v_stop_boxed_785_; uint8_t v_res_786_; lean_object* v_r_787_; 
v___x_8627__boxed_783_ = lean_unbox(v___x_779_);
v_i_boxed_784_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_782_);
lean_dec(v_stop_782_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(v___x_8627__boxed_783_, v_as_780_, v_i_boxed_784_, v_stop_boxed_785_);
lean_dec_ref(v_as_780_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(lean_object* v_ref_788_, lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_toCold_793_; lean_object* v_currRecDepth_794_; lean_object* v_ref_795_; uint16_t v_optionFlags_796_; uint8_t v_suppressElabErrors_797_; uint8_t v_isRecordingDeps_798_; lean_object* v_ref_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_toCold_793_ = lean_ctor_get(v___y_790_, 0);
v_currRecDepth_794_ = lean_ctor_get(v___y_790_, 1);
v_ref_795_ = lean_ctor_get(v___y_790_, 2);
v_optionFlags_796_ = lean_ctor_get_uint16(v___y_790_, sizeof(void*)*3);
v_suppressElabErrors_797_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 2);
v_isRecordingDeps_798_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 3);
v_ref_799_ = l_Lean_replaceRef(v_ref_788_, v_ref_795_);
lean_inc(v_currRecDepth_794_);
lean_inc_ref(v_toCold_793_);
v___x_800_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_800_, 0, v_toCold_793_);
lean_ctor_set(v___x_800_, 1, v_currRecDepth_794_);
lean_ctor_set(v___x_800_, 2, v_ref_799_);
lean_ctor_set_uint16(v___x_800_, sizeof(void*)*3, v_optionFlags_796_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*3 + 2, v_suppressElabErrors_797_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*3 + 3, v_isRecordingDeps_798_);
v___x_801_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v_msg_789_, v___x_800_, v___y_791_);
lean_dec_ref_known(v___x_800_, 3);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_ref_802_, lean_object* v_msg_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_ref_802_, v_msg_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v_ref_802_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__0));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__2));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__4));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(lean_object* v_attrName_817_, lean_object* v_declName_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_822_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__1);
v___x_823_ = l_Lean_MessageData_ofName(v_attrName_817_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__3);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = 0;
v___x_828_ = l_Lean_MessageData_ofConstName(v_declName_818_, v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___closed__5);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_831_, v___y_819_, v___y_820_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_attrName_833_, lean_object* v_declName_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_attrName_833_, v_declName_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_838_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(lean_object* v_name_848_, uint8_t v_kind_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___y_859_; 
v___x_853_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_854_ = l_Lean_MessageData_ofName(v_name_848_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
switch(v_kind_849_)
{
case 0:
{
lean_object* v___x_866_; 
v___x_866_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___y_859_ = v___x_866_;
goto v___jp_858_;
}
case 1:
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__5));
v___y_859_ = v___x_867_;
goto v___jp_858_;
}
default: 
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___closed__6));
v___y_859_ = v___x_868_;
goto v___jp_858_;
}
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_inc_ref(v___y_859_);
v___x_860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_860_, 0, v___y_859_);
v___x_861_ = l_Lean_MessageData_ofFormat(v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_857_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_864_, v___y_850_, v___y_851_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_name_869_, lean_object* v_kind_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_kind_boxed_874_; lean_object* v_res_875_; 
v_kind_boxed_874_ = lean_unbox(v_kind_870_);
v_res_875_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_869_, v_kind_boxed_874_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_box(0);
return v___x_878_;
}
else
{
lean_object* v_key_879_; lean_object* v_value_880_; lean_object* v_tail_881_; uint8_t v___x_882_; 
v_key_879_ = lean_ctor_get(v_x_877_, 0);
v_value_880_ = lean_ctor_get(v_x_877_, 1);
v_tail_881_ = lean_ctor_get(v_x_877_, 2);
v___x_882_ = lean_name_eq(v_key_879_, v_a_876_);
if (v___x_882_ == 0)
{
v_x_877_ = v_tail_881_;
goto _start;
}
else
{
lean_object* v___x_884_; 
lean_inc(v_value_880_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_value_880_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___y_893_; 
v_buckets_890_ = lean_ctor_get(v_m_888_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
if (lean_obj_tag(v_a_889_) == 0)
{
uint64_t v___x_907_; 
v___x_907_ = 1723ULL;
v___y_893_ = v___x_907_;
goto v___jp_892_;
}
else
{
uint64_t v_hash_908_; 
v_hash_908_ = lean_ctor_get_uint64(v_a_889_, sizeof(void*)*2);
v___y_893_ = v_hash_908_;
goto v___jp_892_;
}
v___jp_892_:
{
uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v_fold_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_894_ = 32ULL;
v___x_895_ = lean_uint64_shift_right(v___y_893_, v___x_894_);
v_fold_896_ = lean_uint64_xor(v___y_893_, v___x_895_);
v___x_897_ = 16ULL;
v___x_898_ = lean_uint64_shift_right(v_fold_896_, v___x_897_);
v___x_899_ = lean_uint64_xor(v_fold_896_, v___x_898_);
v___x_900_ = lean_uint64_to_usize(v___x_899_);
v___x_901_ = lean_usize_of_nat(v___x_891_);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_sub(v___x_901_, v___x_902_);
v___x_904_ = lean_usize_land(v___x_900_, v___x_903_);
v___x_905_ = lean_array_uget_borrowed(v_buckets_890_, v___x_904_);
v___x_906_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_889_, v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg___boxed(lean_object* v_m_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v_m_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_m_909_);
return v_res_911_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_912_; double v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_float_of_nat(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object* v_cls_917_, lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_ref_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_969_; 
v_ref_922_ = lean_ctor_get(v___y_919_, 2);
v___x_923_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0(v_msg_918_, v___y_919_, v___y_920_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_969_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_969_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_969_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v_traceState_929_; lean_object* v_env_930_; lean_object* v_nextMacroScope_931_; lean_object* v_ngen_932_; lean_object* v_auxDeclNGen_933_; lean_object* v_cache_934_; lean_object* v_recordedDeps_935_; lean_object* v_messages_936_; lean_object* v_infoState_937_; lean_object* v_snapshotTasks_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_968_; 
v___x_928_ = lean_st_ref_take(v___y_920_);
v_traceState_929_ = lean_ctor_get(v___x_928_, 4);
v_env_930_ = lean_ctor_get(v___x_928_, 0);
v_nextMacroScope_931_ = lean_ctor_get(v___x_928_, 1);
v_ngen_932_ = lean_ctor_get(v___x_928_, 2);
v_auxDeclNGen_933_ = lean_ctor_get(v___x_928_, 3);
v_cache_934_ = lean_ctor_get(v___x_928_, 5);
v_recordedDeps_935_ = lean_ctor_get(v___x_928_, 6);
v_messages_936_ = lean_ctor_get(v___x_928_, 7);
v_infoState_937_ = lean_ctor_get(v___x_928_, 8);
v_snapshotTasks_938_ = lean_ctor_get(v___x_928_, 9);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_968_ == 0)
{
v___x_940_ = v___x_928_;
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snapshotTasks_938_);
lean_inc(v_infoState_937_);
lean_inc(v_messages_936_);
lean_inc(v_recordedDeps_935_);
lean_inc(v_cache_934_);
lean_inc(v_traceState_929_);
lean_inc(v_auxDeclNGen_933_);
lean_inc(v_ngen_932_);
lean_inc(v_nextMacroScope_931_);
lean_inc(v_env_930_);
lean_dec(v___x_928_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint64_t v_tid_942_; lean_object* v_traces_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_967_; 
v_tid_942_ = lean_ctor_get_uint64(v_traceState_929_, sizeof(void*)*1);
v_traces_943_ = lean_ctor_get(v_traceState_929_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_traceState_929_);
if (v_isSharedCheck_967_ == 0)
{
v___x_945_ = v_traceState_929_;
v_isShared_946_ = v_isSharedCheck_967_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_traces_943_);
lean_dec(v_traceState_929_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_967_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; double v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_947_ = lean_box(0);
v___x_948_ = lean_box(0);
v___x_949_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__0);
v___x_950_ = 0;
v___x_951_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_952_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_952_, 0, v_cls_917_);
lean_ctor_set(v___x_952_, 1, v___x_948_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
lean_ctor_set_float(v___x_952_, sizeof(void*)*3, v___x_949_);
lean_ctor_set_float(v___x_952_, sizeof(void*)*3 + 8, v___x_949_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*3 + 16, v___x_950_);
v___x_953_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__2));
v___x_954_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v_a_924_);
lean_ctor_set(v___x_954_, 2, v___x_953_);
lean_inc(v_ref_922_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_ref_922_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_PersistentArray_push___redArg(v_traces_943_, v___x_955_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_956_);
v___x_958_ = v___x_945_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_956_);
lean_ctor_set_uint64(v_reuseFailAlloc_966_, sizeof(void*)*1, v_tid_942_);
v___x_958_ = v_reuseFailAlloc_966_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___x_958_);
v___x_960_ = v___x_940_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_env_930_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_nextMacroScope_931_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_ngen_932_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_auxDeclNGen_933_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v_cache_934_);
lean_ctor_set(v_reuseFailAlloc_965_, 6, v_recordedDeps_935_);
lean_ctor_set(v_reuseFailAlloc_965_, 7, v_messages_936_);
lean_ctor_set(v_reuseFailAlloc_965_, 8, v_infoState_937_);
lean_ctor_set(v_reuseFailAlloc_965_, 9, v_snapshotTasks_938_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_st_ref_put(v___y_920_, v___x_960_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_947_);
v___x_963_ = v___x_926_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_947_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___boxed(lean_object* v_cls_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(v_cls_970_, v_msg_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___lam__0(lean_object* v___x_976_, lean_object* v_entry_977_, lean_object* v_s_978_){
_start:
{
lean_object* v_addEntryFn_979_; lean_object* v_importedEntries_980_; lean_object* v_state_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
v_addEntryFn_979_ = lean_ctor_get(v___x_976_, 3);
lean_inc(v_addEntryFn_979_);
lean_dec_ref(v___x_976_);
v_importedEntries_980_ = lean_ctor_get(v_s_978_, 0);
v_state_981_ = lean_ctor_get(v_s_978_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_989_ == 0)
{
v___x_983_ = v_s_978_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_state_981_);
lean_inc(v_importedEntries_980_);
lean_dec(v_s_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_state_985_; lean_object* v___x_987_; 
v_state_985_ = lean_apply_2(v_addEntryFn_979_, v_state_981_, v_entry_977_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_state_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_importedEntries_980_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_state_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(lean_object* v_keys_990_, lean_object* v_i_991_, lean_object* v_k_992_){
_start:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_keys_990_);
v___x_994_ = lean_nat_dec_lt(v_i_991_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_i_991_);
return v___x_994_;
}
else
{
lean_object* v_k_x27_995_; uint8_t v___x_996_; 
v_k_x27_995_ = lean_array_fget_borrowed(v_keys_990_, v_i_991_);
v___x_996_ = l_Lean_instBEqExtraModUse_beq(v_k_992_, v_k_x27_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_i_991_, v___x_997_);
lean_dec(v_i_991_);
v_i_991_ = v___x_998_;
goto _start;
}
else
{
lean_dec(v_i_991_);
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_keys_1000_, lean_object* v_i_1001_, lean_object* v_k_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_keys_1000_, v_i_1001_, v_k_1002_);
lean_dec_ref(v_k_1002_);
lean_dec_ref(v_keys_1000_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(lean_object* v_x_1005_, size_t v_x_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_es_1008_; lean_object* v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; lean_object* v_j_1012_; lean_object* v___x_1013_; 
v_es_1008_ = lean_ctor_get(v_x_1005_, 0);
v___x_1009_ = lean_box(2);
v___x_1010_ = ((size_t)31ULL);
v___x_1011_ = lean_usize_land(v_x_1006_, v___x_1010_);
v_j_1012_ = lean_usize_to_nat(v___x_1011_);
v___x_1013_ = lean_array_get_borrowed(v___x_1009_, v_es_1008_, v_j_1012_);
lean_dec(v_j_1012_);
switch(lean_obj_tag(v___x_1013_))
{
case 0:
{
lean_object* v_key_1014_; uint8_t v___x_1015_; 
v_key_1014_ = lean_ctor_get(v___x_1013_, 0);
v___x_1015_ = l_Lean_instBEqExtraModUse_beq(v_x_1007_, v_key_1014_);
return v___x_1015_;
}
case 1:
{
lean_object* v_node_1016_; size_t v___x_1017_; size_t v___x_1018_; 
v_node_1016_ = lean_ctor_get(v___x_1013_, 0);
v___x_1017_ = ((size_t)5ULL);
v___x_1018_ = lean_usize_shift_right(v_x_1006_, v___x_1017_);
v_x_1005_ = v_node_1016_;
v_x_1006_ = v___x_1018_;
goto _start;
}
default: 
{
uint8_t v___x_1020_; 
v___x_1020_ = 0;
return v___x_1020_;
}
}
}
else
{
lean_object* v_ks_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_ks_1021_ = lean_ctor_get(v_x_1005_, 0);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_ks_1021_, v___x_1022_, v_x_1007_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
size_t v_x_8967__boxed_1027_; uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_x_8967__boxed_1027_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1028_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1024_, v_x_8967__boxed_1027_, v_x_1026_);
lean_dec_ref(v_x_1026_);
lean_dec_ref(v_x_1024_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
uint64_t v___x_1032_; size_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1032_ = l_Lean_instHashableExtraModUse_hash(v_x_1031_);
v___x_1033_ = lean_uint64_to_usize(v___x_1032_);
v___x_1034_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1030_, v___x_1033_, v_x_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_x_1035_, v_x_1036_);
lean_dec_ref(v_x_1036_);
lean_dec_ref(v_x_1035_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__0);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__5));
v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__7));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_cls_1058_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4));
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__11));
v___x_1060_ = l_Lean_Name_append(v___x_1059_, v_cls_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__13));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__15));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_mod_1071_, uint8_t v_isMeta_1072_, lean_object* v_hint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_env_1095_; uint8_t v_isExporting_1096_; lean_object* v_entry_1097_; lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1093_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__2);
v___x_1094_ = lean_st_ref_get(v___y_1075_);
v_env_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_env_1095_);
lean_dec(v___x_1094_);
v_isExporting_1096_ = lean_ctor_get_uint8(v_env_1095_, sizeof(void*)*13);
lean_dec_ref(v_env_1095_);
lean_inc(v_mod_1071_);
v_entry_1097_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1097_, 0, v_mod_1071_);
lean_ctor_set_uint8(v_entry_1097_, sizeof(void*)*1, v_isExporting_1096_);
lean_ctor_set_uint8(v_entry_1097_, sizeof(void*)*1 + 1, v_isMeta_1072_);
v___x_1098_ = lean_st_ref_get(v___y_1075_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v___x_1100_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1101_ = lean_box(1);
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1093_, v___x_1100_, v_env_1099_, v___x_1101_, v___x_1102_);
v___x_1104_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v___x_1103_, v_entry_1097_);
lean_dec(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v_toCold_1105_; lean_object* v_options_1106_; lean_object* v_inheritedTraceOptions_1107_; uint8_t v_hasTrace_1108_; lean_object* v___f_1109_; uint8_t v___x_1110_; lean_object* v___y_1112_; 
v_toCold_1105_ = lean_ctor_get(v___y_1074_, 0);
v_options_1106_ = lean_ctor_get(v_toCold_1105_, 2);
v_inheritedTraceOptions_1107_ = lean_ctor_get(v_toCold_1105_, 11);
v_hasTrace_1108_ = lean_ctor_get_uint8(v_options_1106_, sizeof(void*)*1);
v___f_1109_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_1109_, 0, v___x_1100_);
lean_closure_set(v___f_1109_, 1, v_entry_1097_);
v___x_1110_ = 1;
if (v_hasTrace_1108_ == 0)
{
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___y_1112_ = v___y_1075_;
goto v___jp_1111_;
}
else
{
lean_object* v_cls_1130_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_cls_1130_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__4));
v___x_1150_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__12);
v___x_1151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1107_, v_options_1106_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___y_1112_ = v___y_1075_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1152_; lean_object* v___y_1154_; 
v___x_1152_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__14);
if (v_isExporting_1096_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__19));
v___y_1154_ = v___x_1161_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__20));
v___y_1154_ = v___x_1162_;
goto v___jp_1153_;
}
v___jp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_inc_ref(v___y_1154_);
v___x_1155_ = l_Lean_stringToMessageData(v___y_1154_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1152_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
if (v_isMeta_1072_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__17));
v___y_1137_ = v___x_1158_;
v___y_1138_ = v___x_1159_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1160_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__18));
v___y_1137_ = v___x_1158_;
v___y_1138_ = v___x_1160_;
goto v___jp_1136_;
}
}
}
v___jp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1132_);
lean_ctor_set(v___x_1134_, 1, v___y_1133_);
v___x_1135_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6(v_cls_1130_, v___x_1134_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_dec_ref_known(v___x_1135_, 1);
v___y_1112_ = v___y_1075_;
goto v___jp_1111_;
}
else
{
lean_dec_ref(v___f_1109_);
return v___x_1135_;
}
}
v___jp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
lean_inc_ref(v___y_1138_);
v___x_1139_ = l_Lean_stringToMessageData(v___y_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__6);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_ofName(v_mod_1071_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_Name_isAnonymous(v_hint_1073_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__8);
v___x_1147_ = l_Lean_MessageData_ofName(v_hint_1073_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___y_1132_ = v___x_1144_;
v___y_1133_ = v___x_1148_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_hint_1073_);
v___x_1149_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__9);
v___y_1132_ = v___x_1144_;
v___y_1133_ = v___x_1149_;
goto v___jp_1131_;
}
}
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v_toEnvExtension_1114_; lean_object* v_env_1115_; lean_object* v_nextMacroScope_1116_; lean_object* v_ngen_1117_; lean_object* v_auxDeclNGen_1118_; lean_object* v_traceState_1119_; lean_object* v_recordedDeps_1120_; lean_object* v_messages_1121_; lean_object* v_infoState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v_asyncMode_1124_; uint8_t v_logWrites_1125_; lean_object* v___x_1126_; 
v___x_1113_ = lean_st_ref_take(v___y_1112_);
v_toEnvExtension_1114_ = lean_ctor_get(v___x_1100_, 0);
v_env_1115_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1115_);
v_nextMacroScope_1116_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_nextMacroScope_1116_);
v_ngen_1117_ = lean_ctor_get(v___x_1113_, 2);
lean_inc_ref(v_ngen_1117_);
v_auxDeclNGen_1118_ = lean_ctor_get(v___x_1113_, 3);
lean_inc_ref(v_auxDeclNGen_1118_);
v_traceState_1119_ = lean_ctor_get(v___x_1113_, 4);
lean_inc_ref(v_traceState_1119_);
v_recordedDeps_1120_ = lean_ctor_get(v___x_1113_, 6);
lean_inc_ref(v_recordedDeps_1120_);
v_messages_1121_ = lean_ctor_get(v___x_1113_, 7);
lean_inc_ref(v_messages_1121_);
v_infoState_1122_ = lean_ctor_get(v___x_1113_, 8);
lean_inc_ref(v_infoState_1122_);
v_snapshotTasks_1123_ = lean_ctor_get(v___x_1113_, 9);
lean_inc_ref(v_snapshotTasks_1123_);
lean_dec(v___x_1113_);
v_asyncMode_1124_ = lean_ctor_get(v_toEnvExtension_1114_, 2);
v_logWrites_1125_ = lean_ctor_get_uint8(v_toEnvExtension_1114_, sizeof(void*)*6);
v___x_1126_ = lean_box(0);
if (v_logWrites_1125_ == 0)
{
lean_object* v___x_1127_; 
lean_inc_ref(v_toEnvExtension_1114_);
v___x_1127_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1114_, v_env_1115_, v___f_1109_, v_asyncMode_1124_, v___x_1102_, v___x_1110_);
v___y_1078_ = v_infoState_1122_;
v___y_1079_ = v_messages_1121_;
v___y_1080_ = v_auxDeclNGen_1118_;
v___y_1081_ = v_ngen_1117_;
v___y_1082_ = v_snapshotTasks_1123_;
v___y_1083_ = v___y_1112_;
v___y_1084_ = v_recordedDeps_1120_;
v___y_1085_ = v_traceState_1119_;
v___y_1086_ = v___x_1126_;
v___y_1087_ = v_nextMacroScope_1116_;
v___y_1088_ = v___x_1127_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_inc_ref_n(v_toEnvExtension_1114_, 2);
v___x_1128_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1114_, v_env_1115_);
lean_dec_ref(v_env_1115_);
v___x_1129_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1114_, v___x_1128_, v___f_1109_, v_asyncMode_1124_, v___x_1102_, v___x_1110_);
v___y_1078_ = v_infoState_1122_;
v___y_1079_ = v_messages_1121_;
v___y_1080_ = v_auxDeclNGen_1118_;
v___y_1081_ = v_ngen_1117_;
v___y_1082_ = v_snapshotTasks_1123_;
v___y_1083_ = v___y_1112_;
v___y_1084_ = v_recordedDeps_1120_;
v___y_1085_ = v_traceState_1119_;
v___y_1086_ = v___x_1126_;
v___y_1087_ = v_nextMacroScope_1116_;
v___y_1088_ = v___x_1129_;
goto v___jp_1077_;
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec_ref_known(v_entry_1097_, 1);
lean_dec(v_hint_1073_);
lean_dec(v_mod_1071_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
v___jp_1077_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1089_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_1090_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1090_, 0, v___y_1088_);
lean_ctor_set(v___x_1090_, 1, v___y_1087_);
lean_ctor_set(v___x_1090_, 2, v___y_1081_);
lean_ctor_set(v___x_1090_, 3, v___y_1080_);
lean_ctor_set(v___x_1090_, 4, v___y_1085_);
lean_ctor_set(v___x_1090_, 5, v___x_1089_);
lean_ctor_set(v___x_1090_, 6, v___y_1084_);
lean_ctor_set(v___x_1090_, 7, v___y_1079_);
lean_ctor_set(v___x_1090_, 8, v___y_1078_);
lean_ctor_set(v___x_1090_, 9, v___y_1082_);
v___x_1091_ = lean_st_ref_put(v___y_1083_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___y_1086_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_mod_1165_, lean_object* v_isMeta_1166_, lean_object* v_hint_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_isMeta_boxed_1171_; lean_object* v_res_1172_; 
v_isMeta_boxed_1171_ = lean_unbox(v_isMeta_1166_);
v_res_1172_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_mod_1165_, v_isMeta_boxed_1171_, v_hint_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(lean_object* v___x_1173_, lean_object* v_declName_1174_, lean_object* v_as_1175_, size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_declName_1174_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_b_1178_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v_modules_1185_; lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v_toImport_1189_; lean_object* v_module_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; 
v___x_1184_ = l_Lean_Environment_header(v___x_1173_);
v_modules_1185_ = lean_ctor_get(v___x_1184_, 3);
lean_inc_ref(v_modules_1185_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1187_ = lean_array_uget_borrowed(v_as_1175_, v_i_1177_);
v___x_1188_ = lean_array_get(v___x_1186_, v_modules_1185_, v_a_1187_);
lean_dec_ref(v_modules_1185_);
v_toImport_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_toImport_1189_);
lean_dec(v___x_1188_);
v_module_1190_ = lean_ctor_get(v_toImport_1189_, 0);
lean_inc(v_module_1190_);
lean_dec_ref(v_toImport_1189_);
v___x_1191_ = lean_box(0);
v___x_1192_ = 0;
lean_inc(v_declName_1174_);
v___x_1193_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_module_1190_, v___x_1192_, v_declName_1174_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1193_) == 0)
{
size_t v___x_1194_; size_t v___x_1195_; 
lean_dec_ref_known(v___x_1193_, 1);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1177_, v___x_1194_);
v_i_1177_ = v___x_1195_;
v_b_1178_ = v___x_1191_;
goto _start;
}
else
{
lean_dec(v_declName_1174_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v___x_1197_, lean_object* v_declName_1198_, lean_object* v_as_1199_, lean_object* v_sz_1200_, lean_object* v_i_1201_, lean_object* v_b_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1200_);
lean_dec(v_sz_1200_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1201_);
lean_dec(v_i_1201_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(v___x_1197_, v_declName_1198_, v_as_1199_, v_sz_boxed_1206_, v_i_boxed_1207_, v_b_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_as_1199_);
lean_dec_ref(v___x_1197_);
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(lean_object* v_declName_1212_, uint8_t v_isMeta_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_env_1222_; lean_object* v___y_1224_; lean_object* v___x_1237_; 
v___x_1217_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__0);
v___x_1218_ = lean_st_ref_get(v___y_1215_);
v_env_1222_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_env_1222_);
lean_dec(v___x_1218_);
v___x_1237_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1222_, v_declName_1212_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_dec_ref(v_env_1222_);
lean_dec(v_declName_1212_);
goto v___jp_1219_;
}
else
{
lean_object* v_val_1238_; lean_object* v___x_1239_; lean_object* v_modules_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = l_Lean_Environment_header(v_env_1222_);
v_modules_1240_ = lean_ctor_get(v___x_1239_, 3);
lean_inc_ref(v_modules_1240_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_array_get_size(v_modules_1240_);
v___x_1242_ = lean_nat_dec_lt(v_val_1238_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_modules_1240_);
lean_dec(v_val_1238_);
lean_dec_ref(v_env_1222_);
lean_dec(v_declName_1212_);
goto v___jp_1219_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___y_1246_; 
v___x_1243_ = lean_array_fget(v_modules_1240_, v_val_1238_);
lean_dec(v_val_1238_);
lean_dec_ref(v_modules_1240_);
v___x_1244_ = lean_st_ref_get(v___y_1215_);
if (v_isMeta_1213_ == 0)
{
lean_dec(v___x_1244_);
v___y_1246_ = v_isMeta_1213_;
goto v___jp_1245_;
}
else
{
lean_object* v_env_1257_; uint8_t v___x_1258_; 
v_env_1257_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_ref(v_env_1257_);
lean_dec(v___x_1244_);
lean_inc(v_declName_1212_);
v___x_1258_ = l_Lean_isMarkedMeta(v_env_1257_, v_declName_1212_);
if (v___x_1258_ == 0)
{
v___y_1246_ = v_isMeta_1213_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
v___y_1246_ = v___x_1259_;
goto v___jp_1245_;
}
}
v___jp_1245_:
{
lean_object* v_toImport_1247_; lean_object* v_module_1248_; lean_object* v___x_1249_; 
v_toImport_1247_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_toImport_1247_);
lean_dec(v___x_1243_);
v_module_1248_ = lean_ctor_get(v_toImport_1247_, 0);
lean_inc(v_module_1248_);
lean_dec_ref(v_toImport_1247_);
lean_inc(v_declName_1212_);
v___x_1249_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4(v_module_1248_, v___y_1246_, v_declName_1212_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1249_, 1);
v___x_1250_ = l_Lean_indirectModUseExt;
v___x_1251_ = lean_box(1);
v___x_1252_ = lean_box(0);
lean_inc_ref(v_env_1222_);
v___x_1253_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1217_, v___x_1250_, v_env_1222_, v___x_1251_, v___x_1252_);
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v___x_1253_, v_declName_1212_);
lean_dec(v___x_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___closed__1));
v___y_1224_ = v___x_1255_;
goto v___jp_1223_;
}
else
{
lean_object* v_val_1256_; 
v_val_1256_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v___x_1254_, 1);
v___y_1224_ = v_val_1256_;
goto v___jp_1223_;
}
}
else
{
lean_dec_ref(v_env_1222_);
lean_dec(v_declName_1212_);
return v___x_1249_;
}
}
}
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1225_ = lean_box(0);
v_sz_1226_ = lean_array_size(v___y_1224_);
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__5(v_env_1222_, v_declName_1212_, v___y_1224_, v_sz_1226_, v___x_1227_, v___x_1225_, v___y_1214_, v___y_1215_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_env_1222_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1225_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1225_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
return v___x_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1260_, lean_object* v_isMeta_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_isMeta_boxed_1265_; lean_object* v_res_1266_; 
v_isMeta_boxed_1265_ = lean_unbox(v_isMeta_1261_);
v_res_1266_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(v_declName_1260_, v_isMeta_boxed_1265_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_name_1297_, lean_object* v_decl_1298_, lean_object* v_stx_1299_, uint8_t v_kind_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v_nextMacroScope_1307_; lean_object* v_ngen_1308_; lean_object* v_auxDeclNGen_1309_; lean_object* v_traceState_1310_; lean_object* v_recordedDeps_1311_; lean_object* v_messages_1312_; lean_object* v_infoState_1313_; lean_object* v_snapshotTasks_1314_; lean_object* v___y_1315_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = 0;
v___x_1455_ = l_Lean_instBEqAttributeKind_beq(v_kind_1300_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_stx_1299_);
lean_dec(v_decl_1298_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v___x_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1292_);
v___x_1456_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_1297_, v_kind_1300_, v___y_1301_, v___y_1302_);
return v___x_1456_;
}
else
{
goto v___jp_1449_;
}
v___jp_1304_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_1317_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1315_);
lean_ctor_set(v___x_1317_, 1, v_nextMacroScope_1307_);
lean_ctor_set(v___x_1317_, 2, v_ngen_1308_);
lean_ctor_set(v___x_1317_, 3, v_auxDeclNGen_1309_);
lean_ctor_set(v___x_1317_, 4, v_traceState_1310_);
lean_ctor_set(v___x_1317_, 5, v___x_1316_);
lean_ctor_set(v___x_1317_, 6, v_recordedDeps_1311_);
lean_ctor_set(v___x_1317_, 7, v_messages_1312_);
lean_ctor_set(v___x_1317_, 8, v_infoState_1313_);
lean_ctor_set(v___x_1317_, 9, v_snapshotTasks_1314_);
v___x_1318_ = lean_st_ref_put(v___y_1305_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1306_);
return v___x_1319_;
}
v___jp_1320_:
{
lean_object* v___x_1324_; lean_object* v_env_1325_; lean_object* v_nextMacroScope_1326_; lean_object* v_ngen_1327_; lean_object* v_auxDeclNGen_1328_; lean_object* v_traceState_1329_; lean_object* v_recordedDeps_1330_; lean_object* v_messages_1331_; lean_object* v_infoState_1332_; lean_object* v_snapshotTasks_1333_; lean_object* v___x_1334_; lean_object* v_toEnvExtension_1335_; lean_object* v_addEntryFn_1336_; lean_object* v_asyncMode_1337_; uint8_t v_logWrites_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___f_1341_; 
v___x_1324_ = lean_st_ref_take(v___y_1323_);
v_env_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1325_);
v_nextMacroScope_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_nextMacroScope_1326_);
v_ngen_1327_ = lean_ctor_get(v___x_1324_, 2);
lean_inc_ref(v_ngen_1327_);
v_auxDeclNGen_1328_ = lean_ctor_get(v___x_1324_, 3);
lean_inc_ref(v_auxDeclNGen_1328_);
v_traceState_1329_ = lean_ctor_get(v___x_1324_, 4);
lean_inc_ref(v_traceState_1329_);
v_recordedDeps_1330_ = lean_ctor_get(v___x_1324_, 6);
lean_inc_ref(v_recordedDeps_1330_);
v_messages_1331_ = lean_ctor_get(v___x_1324_, 7);
lean_inc_ref(v_messages_1331_);
v_infoState_1332_ = lean_ctor_get(v___x_1324_, 8);
lean_inc_ref(v_infoState_1332_);
v_snapshotTasks_1333_ = lean_ctor_get(v___x_1324_, 9);
lean_inc_ref(v_snapshotTasks_1333_);
lean_dec(v___x_1324_);
v___x_1334_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1335_ = lean_ctor_get(v___x_1334_, 0);
v_addEntryFn_1336_ = lean_ctor_get(v___x_1334_, 3);
v_asyncMode_1337_ = lean_ctor_get(v_toEnvExtension_1335_, 2);
v_logWrites_1338_ = lean_ctor_get_uint8(v_toEnvExtension_1335_, sizeof(void*)*6);
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_decl_1298_);
lean_ctor_set(v___x_1340_, 1, v___y_1321_);
lean_inc(v_addEntryFn_1336_);
v___f_1341_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_1341_, 0, v_addEntryFn_1336_);
lean_closure_set(v___f_1341_, 1, v___x_1340_);
if (v_logWrites_1338_ == 0)
{
lean_object* v___x_1342_; 
lean_inc_ref(v_toEnvExtension_1335_);
v___x_1342_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1335_, v_env_1325_, v___f_1341_, v_asyncMode_1337_, v___x_1292_, v___y_1322_);
v___y_1305_ = v___y_1323_;
v___y_1306_ = v___x_1339_;
v_nextMacroScope_1307_ = v_nextMacroScope_1326_;
v_ngen_1308_ = v_ngen_1327_;
v_auxDeclNGen_1309_ = v_auxDeclNGen_1328_;
v_traceState_1310_ = v_traceState_1329_;
v_recordedDeps_1311_ = v_recordedDeps_1330_;
v_messages_1312_ = v_messages_1331_;
v_infoState_1313_ = v_infoState_1332_;
v_snapshotTasks_1314_ = v_snapshotTasks_1333_;
v___y_1315_ = v___x_1342_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_inc_ref_n(v_toEnvExtension_1335_, 2);
v___x_1343_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1335_, v_env_1325_);
lean_dec_ref(v_env_1325_);
v___x_1344_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1335_, v___x_1343_, v___f_1341_, v_asyncMode_1337_, v___x_1292_, v___y_1322_);
v___y_1305_ = v___y_1323_;
v___y_1306_ = v___x_1339_;
v_nextMacroScope_1307_ = v_nextMacroScope_1326_;
v_ngen_1308_ = v_ngen_1327_;
v_auxDeclNGen_1309_ = v_auxDeclNGen_1328_;
v_traceState_1310_ = v_traceState_1329_;
v_recordedDeps_1311_ = v_recordedDeps_1330_;
v_messages_1312_ = v_messages_1331_;
v_infoState_1313_ = v_infoState_1332_;
v_snapshotTasks_1314_ = v_snapshotTasks_1333_;
v___y_1315_ = v___x_1344_;
goto v___jp_1304_;
}
}
v___jp_1345_:
{
lean_object* v___x_1350_; lean_object* v_env_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_st_ref_get(v___y_1349_);
v_env_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_env_1351_);
lean_dec(v___x_1350_);
lean_inc(v___y_1346_);
v___x_1352_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1351_, v___y_1346_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_decl_1298_);
lean_dec(v___x_1292_);
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1355_ = l_Lean_MessageData_ofName(v___y_1346_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_MessageData_ofName(v_val_1353_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1354_);
v___x_1362_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1361_, v___y_1348_, v___y_1349_);
return v___x_1362_;
}
else
{
lean_dec(v___x_1352_);
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1349_;
goto v___jp_1320_;
}
}
v___jp_1363_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___y_1364_);
v___x_1370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1371_ = l_Lean_MessageData_ofName(v_decl_1298_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_inc_ref(v___y_1369_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___y_1369_);
v___x_1376_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__16);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_array_to_list(v___y_1365_);
v___x_1379_ = l_Lean_MessageData_andList(v___x_1378_);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1377_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1382_, v___y_1368_, v___y_1367_);
return v___x_1383_;
}
v___jp_1384_:
{
size_t v_sz_1391_; size_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_sz_1391_ = lean_array_size(v___y_1388_);
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1(v_sz_1391_, v___x_1392_, v___y_1388_);
v___x_1394_ = lean_array_get_size(v___x_1393_);
v___x_1395_ = lean_nat_dec_lt(v___y_1385_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___y_1364_ = v___y_1386_;
v___y_1365_ = v___x_1393_;
v___y_1366_ = v___y_1387_;
v___y_1367_ = v___y_1390_;
v___y_1368_ = v___y_1389_;
v___y_1369_ = v___x_1396_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___y_1364_ = v___y_1386_;
v___y_1365_ = v___x_1393_;
v___y_1366_ = v___y_1387_;
v___y_1367_ = v___y_1390_;
v___y_1368_ = v___y_1389_;
v___y_1369_ = v___x_1397_;
goto v___jp_1363_;
}
}
v___jp_1398_:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1404_ = lean_st_ref_get(v___y_1403_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
lean_inc(v_decl_1298_);
v___x_1406_ = l_Lean_Parser_getSyntaxNodeKindCategories(v_env_1405_, v_decl_1298_);
v___x_1407_ = lean_array_get_size(v___x_1406_);
v___x_1408_ = lean_nat_dec_eq(v___x_1407_, v___x_1293_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_lt(v___x_1293_, v___x_1407_);
if (v___x_1409_ == 0)
{
lean_dec(v___x_1292_);
v___y_1385_ = v___y_1399_;
v___y_1386_ = v___y_1400_;
v___y_1387_ = v___y_1401_;
v___y_1388_ = v___x_1406_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___y_1403_;
goto v___jp_1384_;
}
else
{
if (v___x_1409_ == 0)
{
lean_dec(v___x_1292_);
v___y_1385_ = v___y_1399_;
v___y_1386_ = v___y_1400_;
v___y_1387_ = v___y_1401_;
v___y_1388_ = v___x_1406_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___y_1403_;
goto v___jp_1384_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1407_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__2(v___y_1401_, v___x_1406_, v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_dec(v___x_1292_);
v___y_1385_ = v___y_1399_;
v___y_1386_ = v___y_1400_;
v___y_1387_ = v___y_1401_;
v___y_1388_ = v___x_1406_;
v___y_1389_ = v___y_1402_;
v___y_1390_ = v___y_1403_;
goto v___jp_1384_;
}
else
{
lean_dec_ref(v___x_1406_);
v___y_1346_ = v___y_1400_;
v___y_1347_ = v___y_1401_;
v___y_1348_ = v___y_1402_;
v___y_1349_ = v___y_1403_;
goto v___jp_1345_;
}
}
}
}
else
{
lean_dec_ref(v___x_1406_);
v___y_1346_ = v___y_1400_;
v___y_1347_ = v___y_1401_;
v___y_1348_ = v___y_1402_;
v___y_1349_ = v___y_1403_;
goto v___jp_1345_;
}
}
v___jp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1417_ = l_Lean_Name_mkStr4(v___x_1294_, v___x_1295_, v___x_1416_, v___x_1296_);
lean_inc(v_stx_1299_);
v___x_1418_ = l_Lean_Syntax_isOfKind(v_stx_1299_, v___x_1417_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_stx_1299_);
lean_dec(v_decl_1298_);
lean_dec(v___x_1292_);
v___x_1419_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1420_ = l_Lean_MessageData_ofName(v_name_1297_);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_1423_, v___y_1414_, v___y_1415_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v_name_1297_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_1299_, v___x_1425_);
lean_dec(v_stx_1299_);
v___x_1427_ = lean_box(0);
lean_inc(v___x_1426_);
v___x_1428_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1426_, v___x_1427_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc_n(v_a_1429_, 2);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = 0;
v___x_1431_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3(v_a_1429_, v___x_1430_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; lean_object* v_env_1433_; uint8_t v___x_1434_; 
lean_dec_ref_known(v___x_1431_, 1);
v___x_1432_ = lean_st_ref_get(v___y_1415_);
v_env_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_env_1433_);
lean_dec(v___x_1432_);
v___x_1434_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1433_, v_a_1429_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v_decl_1298_);
lean_dec(v___x_1292_);
v___x_1435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_1436_ = l_Lean_MessageData_ofName(v_a_1429_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v___x_1426_, v___x_1439_, v___y_1414_, v___y_1415_);
lean_dec(v___x_1426_);
return v___x_1440_;
}
else
{
lean_dec(v___x_1426_);
v___y_1399_ = v___x_1425_;
v___y_1400_ = v_a_1429_;
v___y_1401_ = v___x_1418_;
v___y_1402_ = v___y_1414_;
v___y_1403_ = v___y_1415_;
goto v___jp_1398_;
}
}
else
{
lean_dec(v_a_1429_);
lean_dec(v___x_1426_);
lean_dec(v_decl_1298_);
lean_dec(v___x_1292_);
return v___x_1431_;
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v___x_1426_);
lean_dec(v_decl_1298_);
lean_dec(v___x_1292_);
v_a_1441_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1428_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1428_);
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
v___jp_1449_:
{
lean_object* v___x_1450_; lean_object* v_env_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_st_ref_get(v___y_1302_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1451_, v_decl_1298_);
lean_dec_ref(v_env_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
v___y_1414_ = v___y_1301_;
v___y_1415_ = v___y_1302_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1453_; 
lean_dec_ref_known(v___x_1452_, 1);
lean_dec(v_stx_1299_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v___x_1295_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1292_);
v___x_1453_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_name_1297_, v_decl_1298_, v___y_1301_, v___y_1302_);
return v___x_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object* v___x_1457_, lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v___x_1461_, lean_object* v_name_1462_, lean_object* v_decl_1463_, lean_object* v_stx_1464_, lean_object* v_kind_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v_kind_boxed_1469_; lean_object* v_res_1470_; 
v_kind_boxed_1469_ = lean_unbox(v_kind_1465_);
v_res_1470_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(v___x_1457_, v___x_1458_, v___x_1459_, v___x_1460_, v___x_1461_, v_name_1462_, v_decl_1463_, v_stx_1464_, v_kind_boxed_1469_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___x_1458_);
return v_res_1470_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_unsigned_to_nat(2574034933u);
v___x_1535_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1536_ = l_Lean_Name_num___override(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1539_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1540_ = l_Lean_Name_str___override(v___x_1539_, v___x_1538_);
return v___x_1540_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1543_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1544_ = l_Lean_Name_str___override(v___x_1543_, v___x_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(2u);
v___x_1546_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1547_ = l_Lean_Name_num___override(v___x_1546_, v___x_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v_name_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1549_ = 1;
v___x_1550_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v_name_1551_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1552_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1553_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_name_1551_);
lean_ctor_set(v___x_1553_, 2, v___x_1550_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*3, v___x_1549_);
return v___x_1553_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___f_1554_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___f_1555_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_1556_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___f_1555_);
lean_ctor_set(v___x_1557_, 2, v___f_1554_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_1560_ = l_Lean_registerBuiltinAttribute(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2____boxed(lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_();
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1563_, lean_object* v_msg_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v_msg_1564_, v___y_1565_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_msg_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0(v_00_u03b1_1569_, v_msg_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1575_, lean_object* v_ref_1576_, lean_object* v_msg_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_ref_1576_, v_msg_1577_, v___y_1578_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_ref_1583_, lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4(v_00_u03b1_1582_, v_ref_1583_, v_msg_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v_ref_1583_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1589_, lean_object* v_attrName_1590_, lean_object* v_declName_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___redArg(v_attrName_1590_, v_declName_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_attrName_1597_, lean_object* v_declName_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__5(v_00_u03b1_1596_, v_attrName_1597_, v_declName_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1603_, lean_object* v_name_1604_, uint8_t v_kind_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_1604_, v_kind_1605_, v___y_1606_, v___y_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_name_1611_, lean_object* v_kind_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_kind_boxed_1616_; lean_object* v_res_1617_; 
v_kind_boxed_1616_ = lean_unbox(v_kind_1612_);
v_res_1617_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6(v_00_u03b1_1610_, v_name_1611_, v_kind_boxed_1616_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6(lean_object* v_00_u03b2_1618_, lean_object* v_m_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___redArg(v_m_1619_, v_a_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v_00_u03b2_1622_, lean_object* v_m_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6(v_00_u03b2_1622_, v_m_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_m_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_x_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b2_1630_, v_x_1631_, v_x_1632_);
lean_dec_ref(v_x_1632_);
lean_dec_ref(v_x_1631_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9(lean_object* v_00_u03b2_1635_, lean_object* v_a_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___redArg(v_a_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__6_spec__9(v_00_u03b2_1639_, v_a_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec(v_a_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1643_, lean_object* v_x_1644_, size_t v_x_1645_, lean_object* v_x_1646_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___redArg(v_x_1644_, v_x_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
size_t v_x_10102__boxed_1652_; uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_x_10102__boxed_1652_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_res_1653_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9(v_00_u03b2_1648_, v_x_1649_, v_x_10102__boxed_1652_, v_x_1651_);
lean_dec_ref(v_x_1651_);
lean_dec_ref(v_x_1649_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_k_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___redArg(v_keys_1656_, v_i_1659_, v_k_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_keys_1663_, lean_object* v_vals_1664_, lean_object* v_heq_1665_, lean_object* v_i_1666_, lean_object* v_k_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__5_spec__9_spec__12(v_00_u03b2_1662_, v_keys_1663_, v_vals_1664_, v_heq_1665_, v_i_1666_, v_k_1667_);
lean_dec_ref(v_k_1667_);
lean_dec_ref(v_vals_1664_);
lean_dec_ref(v_keys_1663_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v_fst_1672_; lean_object* v_snd_1673_; lean_object* v___x_1674_; 
v_fst_1672_ = lean_ctor_get(v_x_1671_, 0);
lean_inc(v_fst_1672_);
v_snd_1673_ = lean_ctor_get(v_x_1671_, 1);
lean_inc(v_snd_1673_);
lean_dec_ref(v_x_1671_);
v___x_1674_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1672_, v_snd_1673_, v_as_1670_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1675_, lean_object* v_x_1676_){
_start:
{
if (lean_obj_tag(v_x_1676_) == 0)
{
lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v_l_1679_; lean_object* v_r_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_k_1677_ = lean_ctor_get(v_x_1676_, 1);
v_v_1678_ = lean_ctor_get(v_x_1676_, 2);
v_l_1679_ = lean_ctor_get(v_x_1676_, 3);
v_r_1680_ = lean_ctor_get(v_x_1676_, 4);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1675_, v_l_1679_);
lean_inc(v_v_1678_);
lean_inc(v_k_1677_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_k_1677_);
lean_ctor_set(v___x_1682_, 1, v_v_1678_);
v___x_1683_ = lean_array_push(v___x_1681_, v___x_1682_);
v_init_1675_ = v___x_1683_;
v_x_1676_ = v_r_1680_;
goto _start;
}
else
{
return v_init_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1685_, v_x_1686_);
lean_dec(v_x_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_1688_, lean_object* v_x2_1689_){
_start:
{
lean_object* v_fst_1690_; lean_object* v_fst_1691_; uint8_t v___x_1692_; 
v_fst_1690_ = lean_ctor_get(v_x1_1688_, 0);
v_fst_1691_ = lean_ctor_get(v_x2_1689_, 0);
v___x_1692_ = l_Lean_Name_quickLt(v_fst_1690_, v_fst_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_1693_, lean_object* v_x2_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_1693_, v_x2_1694_);
lean_dec_ref(v_x2_1694_);
lean_dec_ref(v_x1_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1697_, lean_object* v_pivot_1698_, lean_object* v_as_1699_, lean_object* v_i_1700_, lean_object* v_k_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_nat_dec_lt(v_k_1701_, v_hi_1697_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v_k_1701_);
v___x_1703_ = lean_array_fswap(v_as_1699_, v_i_1700_, v_hi_1697_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_i_1700_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v_fst_1706_; lean_object* v_fst_1707_; uint8_t v___x_1708_; 
v___x_1705_ = lean_array_fget_borrowed(v_as_1699_, v_k_1701_);
v_fst_1706_ = lean_ctor_get(v___x_1705_, 0);
v_fst_1707_ = lean_ctor_get(v_pivot_1698_, 0);
v___x_1708_ = l_Lean_Name_quickLt(v_fst_1706_, v_fst_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_k_1701_, v___x_1709_);
lean_dec(v_k_1701_);
v_k_1701_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = lean_array_fswap(v_as_1699_, v_i_1700_, v_k_1701_);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v_i_1700_, v___x_1713_);
lean_dec(v_i_1700_);
v___x_1715_ = lean_nat_add(v_k_1701_, v___x_1713_);
lean_dec(v_k_1701_);
v_as_1699_ = v___x_1712_;
v_i_1700_ = v___x_1714_;
v_k_1701_ = v___x_1715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1717_, lean_object* v_pivot_1718_, lean_object* v_as_1719_, lean_object* v_i_1720_, lean_object* v_k_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1717_, v_pivot_1718_, v_as_1719_, v_i_1720_, v_k_1721_);
lean_dec_ref(v_pivot_1718_);
lean_dec(v_hi_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1723_, lean_object* v_as_1724_, lean_object* v_lo_1725_, lean_object* v_hi_1726_){
_start:
{
lean_object* v___y_1728_; uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_lt(v_lo_1725_, v_hi_1726_);
if (v___x_1738_ == 0)
{
lean_dec(v_lo_1725_);
return v_as_1724_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_mid_1741_; lean_object* v___y_1743_; lean_object* v___y_1749_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1739_ = lean_nat_add(v_lo_1725_, v_hi_1726_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v_mid_1741_ = lean_nat_shiftr(v___x_1739_, v___x_1740_);
lean_dec(v___x_1739_);
v___x_1754_ = lean_array_fget_borrowed(v_as_1724_, v_mid_1741_);
v___x_1755_ = lean_array_fget_borrowed(v_as_1724_, v_lo_1725_);
v___x_1756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
v___y_1749_ = v_as_1724_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_array_fswap(v_as_1724_, v_lo_1725_, v_mid_1741_);
v___y_1749_ = v___x_1757_;
goto v___jp_1748_;
}
v___jp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_array_fget_borrowed(v___y_1743_, v_mid_1741_);
v___x_1745_ = lean_array_fget_borrowed(v___y_1743_, v_hi_1726_);
v___x_1746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_dec(v_mid_1741_);
v___y_1728_ = v___y_1743_;
goto v___jp_1727_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_array_fswap(v___y_1743_, v_mid_1741_, v_hi_1726_);
lean_dec(v_mid_1741_);
v___y_1728_ = v___x_1747_;
goto v___jp_1727_;
}
}
v___jp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = lean_array_fget_borrowed(v___y_1749_, v_hi_1726_);
v___x_1751_ = lean_array_fget_borrowed(v___y_1749_, v_lo_1725_);
v___x_1752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
v___y_1743_ = v___y_1749_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_array_fswap(v___y_1749_, v_lo_1725_, v_hi_1726_);
v___y_1743_ = v___x_1753_;
goto v___jp_1742_;
}
}
}
v___jp_1727_:
{
lean_object* v_pivot_1729_; lean_object* v___x_1730_; lean_object* v_fst_1731_; lean_object* v_snd_1732_; uint8_t v___x_1733_; 
v_pivot_1729_ = lean_array_fget(v___y_1728_, v_hi_1726_);
lean_inc_n(v_lo_1725_, 2);
v___x_1730_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1726_, v_pivot_1729_, v___y_1728_, v_lo_1725_, v_lo_1725_);
lean_dec(v_pivot_1729_);
v_fst_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_fst_1731_);
v_snd_1732_ = lean_ctor_get(v___x_1730_, 1);
lean_inc(v_snd_1732_);
lean_dec_ref(v___x_1730_);
v___x_1733_ = lean_nat_dec_le(v_hi_1726_, v_fst_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1723_, v_snd_1732_, v_lo_1725_, v_fst_1731_);
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_nat_add(v_fst_1731_, v___x_1735_);
lean_dec(v_fst_1731_);
v_as_1724_ = v___x_1734_;
v_lo_1725_ = v___x_1736_;
goto _start;
}
else
{
lean_dec(v_fst_1731_);
lean_dec(v_lo_1725_);
return v_snd_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1758_, lean_object* v_as_1759_, lean_object* v_lo_1760_, lean_object* v_hi_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1758_, v_as_1759_, v_lo_1760_, v_hi_1761_);
lean_dec(v_hi_1761_);
lean_dec(v_n_1758_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_1765_, lean_object* v_s_1766_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v___x_1776_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1769_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1768_, v_s_1766_);
v___x_1770_ = lean_array_get_size(v___x_1769_);
v___x_1776_ = lean_nat_dec_eq(v___x_1770_, v___x_1767_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___y_1780_; uint8_t v___x_1782_; 
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_sub(v___x_1770_, v___x_1777_);
v___x_1782_ = lean_nat_dec_le(v___x_1767_, v___x_1778_);
if (v___x_1782_ == 0)
{
lean_inc(v___x_1778_);
v___y_1780_ = v___x_1778_;
goto v___jp_1779_;
}
else
{
v___y_1780_ = v___x_1767_;
goto v___jp_1779_;
}
v___jp_1779_:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_le(v___y_1780_, v___x_1778_);
if (v___x_1781_ == 0)
{
lean_dec(v___x_1778_);
lean_inc(v___y_1780_);
v___y_1772_ = v___y_1780_;
v___y_1773_ = v___y_1780_;
goto v___jp_1771_;
}
else
{
v___y_1772_ = v___y_1780_;
v___y_1773_ = v___x_1778_;
goto v___jp_1771_;
}
}
}
else
{
lean_object* v___x_1783_; 
lean_inc_ref_n(v___x_1769_, 2);
v___x_1783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1769_);
lean_ctor_set(v___x_1783_, 1, v___x_1769_);
lean_ctor_set(v___x_1783_, 2, v___x_1769_);
return v___x_1783_;
}
v___jp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1770_, v___x_1769_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_inc_ref_n(v___x_1774_, 2);
v___x_1775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
lean_ctor_set(v___x_1775_, 2, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_1784_, lean_object* v_s_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_1784_, v_s_1785_);
lean_dec(v_s_1785_);
lean_dec_ref(v_x_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1789_, v_es_1787_);
v___x_1791_ = lean_array_get_size(v___x_1790_);
v___x_1792_ = lean_nat_dec_eq(v___x_1791_, v___x_1788_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___y_1796_; uint8_t v___x_1800_; 
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_nat_sub(v___x_1791_, v___x_1793_);
v___x_1800_ = lean_nat_dec_le(v___x_1788_, v___x_1794_);
if (v___x_1800_ == 0)
{
lean_inc(v___x_1794_);
v___y_1796_ = v___x_1794_;
goto v___jp_1795_;
}
else
{
v___y_1796_ = v___x_1788_;
goto v___jp_1795_;
}
v___jp_1795_:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_nat_dec_le(v___y_1796_, v___x_1794_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_dec(v___x_1794_);
lean_inc(v___y_1796_);
v___x_1798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1791_, v___x_1790_, v___y_1796_, v___y_1796_);
lean_dec(v___y_1796_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1791_, v___x_1790_, v___y_1796_, v___x_1794_);
lean_dec(v___x_1794_);
return v___x_1799_;
}
}
}
else
{
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_1801_);
lean_dec(v_es_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_1803_, lean_object* v_x_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_1808_, v_x_1809_, v___y_1810_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v_x_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1840_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_1843_, lean_object* v_t_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1843_, v_t_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_1846_, lean_object* v_t_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_1846_, v_t_1847_);
lean_dec(v_t_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_1849_, lean_object* v_as_1850_, lean_object* v_lo_1851_, lean_object* v_hi_1852_, lean_object* v_w_1853_, lean_object* v_hlo_1854_, lean_object* v_hhi_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_1849_, v_as_1850_, v_lo_1851_, v_hi_1852_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1857_, lean_object* v_as_1858_, lean_object* v_lo_1859_, lean_object* v_hi_1860_, lean_object* v_w_1861_, lean_object* v_hlo_1862_, lean_object* v_hhi_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_1857_, v_as_1858_, v_lo_1859_, v_hi_1860_, v_w_1861_, v_hlo_1862_, v_hhi_1863_);
lean_dec(v_hi_1860_);
lean_dec(v_n_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_1865_, lean_object* v_lo_1866_, lean_object* v_hi_1867_, lean_object* v_hhi_1868_, lean_object* v_pivot_1869_, lean_object* v_as_1870_, lean_object* v_i_1871_, lean_object* v_k_1872_, lean_object* v_ilo_1873_, lean_object* v_ik_1874_, lean_object* v_w_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1867_, v_pivot_1869_, v_as_1870_, v_i_1871_, v_k_1872_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_1877_, lean_object* v_lo_1878_, lean_object* v_hi_1879_, lean_object* v_hhi_1880_, lean_object* v_pivot_1881_, lean_object* v_as_1882_, lean_object* v_i_1883_, lean_object* v_k_1884_, lean_object* v_ilo_1885_, lean_object* v_ik_1886_, lean_object* v_w_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(v_n_1877_, v_lo_1878_, v_hi_1879_, v_hhi_1880_, v_pivot_1881_, v_as_1882_, v_i_1883_, v_k_1884_, v_ilo_1885_, v_ik_1886_, v_w_1887_);
lean_dec_ref(v_pivot_1881_);
lean_dec(v_hi_1879_);
lean_dec(v_lo_1878_);
lean_dec(v_n_1877_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_1893_, lean_object* v___x_1894_, lean_object* v_toPure_1895_, lean_object* v___f_1896_, lean_object* v_env_1897_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1897_, v_tag_1893_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v_toEnvExtension_1903_; lean_object* v_asyncMode_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref(v___f_1896_);
v___x_1902_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_1903_ = lean_ctor_get(v___x_1902_, 0);
v_asyncMode_1904_ = lean_ctor_get(v_toEnvExtension_1903_, 2);
v___x_1905_ = lean_box(0);
v___x_1906_ = 0;
v___x_1907_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1894_, v___x_1902_, v_env_1897_, v_asyncMode_1904_, v___x_1905_, v___x_1906_);
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1907_, v_tag_1893_);
lean_dec(v_tag_1893_);
lean_dec(v___x_1907_);
v___x_1909_ = lean_apply_2(v_toPure_1895_, lean_box(0), v___x_1908_);
return v___x_1909_;
}
else
{
lean_object* v_val_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v_val_1910_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1911_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_1912_ = 0;
v___x_1913_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1894_, v___x_1911_, v_env_1897_, v_val_1910_, v___x_1912_);
lean_dec(v_val_1910_);
lean_dec_ref(v_env_1897_);
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v___x_1913_);
v___x_1916_ = lean_nat_dec_lt(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v___x_1913_);
lean_dec_ref(v___f_1896_);
lean_dec(v_tag_1893_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_sub(v___x_1915_, v___x_1917_);
v___x_1919_ = lean_nat_dec_le(v___x_1914_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_dec(v___x_1918_);
lean_dec_ref(v___x_1913_);
lean_dec_ref(v___f_1896_);
lean_dec(v_tag_1893_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_tag_1893_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_1923_ = l_Array_binSearchAux___redArg(v___f_1896_, v___x_1922_, v___x_1913_, v___x_1921_, v___x_1914_, v___x_1918_);
lean_dec_ref(v___x_1913_);
if (lean_obj_tag(v___x_1923_) == 0)
{
goto v___jp_1898_;
}
else
{
lean_object* v_val_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v_val_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_val_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_snd_1928_; lean_object* v___x_1930_; 
v_snd_1928_ = lean_ctor_get(v_val_1924_, 1);
lean_inc(v_snd_1928_);
lean_dec(v_val_1924_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_snd_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_snd_1928_);
v___x_1930_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_apply_2(v_toPure_1895_, lean_box(0), v___x_1930_);
return v___x_1931_;
}
}
}
}
}
}
v___jp_1898_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_apply_2(v_toPure_1895_, lean_box(0), v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_tag_1937_){
_start:
{
lean_object* v_toApplicative_1938_; lean_object* v_toBind_1939_; lean_object* v_getEnv_1940_; lean_object* v_toPure_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; 
v_toApplicative_1938_ = lean_ctor_get(v_inst_1935_, 0);
lean_inc_ref(v_toApplicative_1938_);
v_toBind_1939_ = lean_ctor_get(v_inst_1935_, 1);
lean_inc(v_toBind_1939_);
lean_dec_ref(v_inst_1935_);
v_getEnv_1940_ = lean_ctor_get(v_inst_1936_, 0);
lean_inc(v_getEnv_1940_);
lean_dec_ref(v_inst_1936_);
v_toPure_1941_ = lean_ctor_get(v_toApplicative_1938_, 1);
lean_inc(v_toPure_1941_);
lean_dec_ref(v_toApplicative_1938_);
v___f_1942_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0));
v___x_1943_ = lean_box(1);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1944_, 0, v_tag_1937_);
lean_closure_set(v___f_1944_, 1, v___x_1943_);
lean_closure_set(v___f_1944_, 2, v_toPure_1941_);
lean_closure_set(v___f_1944_, 3, v___f_1942_);
v___x_1945_ = lean_apply_4(v_toBind_1939_, lean_box(0), lean_box(0), v_getEnv_1940_, v___f_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_tag_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_1947_, v_inst_1948_, v_tag_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_1951_, lean_object* v_k_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_array_push(v_l_1951_, v_k_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_1955_, lean_object* v_x2_1956_){
_start:
{
uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = 1;
v___x_1958_ = l_Lean_Name_toString(v_x1_1955_, v___x_1957_);
v___x_1959_ = l_Lean_Name_toString(v_x2_1956_, v___x_1957_);
v___x_1960_ = lean_string_dec_lt(v___x_1958_, v___x_1959_);
lean_dec_ref(v___x_1959_);
lean_dec_ref(v___x_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_1961_, lean_object* v_x2_1962_){
_start:
{
uint8_t v_res_1963_; lean_object* v_r_1964_; 
v_res_1963_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_1961_, v_x2_1962_);
v_r_1964_ = lean_box(v_res_1963_);
return v_r_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_1965_, lean_object* v_a_1966_, lean_object* v_b_1967_, lean_object* v_c_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_NameSet_insert(v_c_1968_, v_a_1966_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
v___x_1971_ = lean_apply_2(v_toPure_1965_, lean_box(0), v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_1972_, lean_object* v_a_1973_, lean_object* v_b_1974_, lean_object* v_c_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_1972_, v_a_1973_, v_b_1974_, v_c_1975_);
lean_dec_ref(v_b_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_1977_, lean_object* v_a_1978_, lean_object* v_x_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_fst_1981_; lean_object* v_found_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_fst_1981_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_fst_1981_);
lean_dec_ref(v_a_1978_);
v_found_1982_ = l_Lean_NameSet_insert(v___y_1980_, v_fst_1981_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_found_1982_);
v___x_1984_ = lean_apply_2(v_toPure_1977_, lean_box(0), v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_1985_, lean_object* v___f_1986_, lean_object* v_toBind_1987_, lean_object* v___f_1988_, lean_object* v_a_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_){
_start:
{
size_t v_sz_1992_; size_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_sz_1992_ = lean_array_size(v_a_1989_);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1985_, v_a_1989_, v___f_1986_, v_sz_1992_, v___x_1993_, v___y_1991_);
v___x_1995_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_1994_, v___f_1988_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_1996_, lean_object* v___f_1997_, lean_object* v___f_1998_, lean_object* v_____s_1999_){
_start:
{
lean_object* v___y_2001_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2017_; 
if (lean_obj_tag(v_____s_1999_) == 0)
{
lean_object* v_size_2026_; 
v_size_2026_ = lean_ctor_get(v_____s_1999_, 0);
lean_inc(v_size_2026_);
v___y_2017_ = v_size_2026_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
v___y_2017_ = v___x_2027_;
goto v___jp_2016_;
}
v___jp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_array_to_list(v___y_2001_);
v___x_2003_ = lean_apply_2(v_toPure_1996_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
v___jp_2004_:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1997_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2008_);
lean_dec(v___y_2005_);
v___y_2001_ = v___x_2009_;
goto v___jp_2000_;
}
v___jp_2010_:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_nat_dec_le(v___y_2014_, v___y_2011_);
if (v___x_2015_ == 0)
{
lean_dec(v___y_2011_);
lean_inc(v___y_2014_);
v___y_2005_ = v___y_2012_;
v___y_2006_ = v___y_2013_;
v___y_2007_ = v___y_2014_;
v___y_2008_ = v___y_2014_;
goto v___jp_2004_;
}
else
{
v___y_2005_ = v___y_2012_;
v___y_2006_ = v___y_2013_;
v___y_2007_ = v___y_2014_;
v___y_2008_ = v___y_2011_;
goto v___jp_2004_;
}
}
v___jp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2018_ = lean_mk_empty_array_with_capacity(v___y_2017_);
lean_dec(v___y_2017_);
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1998_, v___x_2018_, v_____s_1999_);
v___x_2020_ = lean_array_get_size(v___x_2019_);
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_nat_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v___x_2020_, v___x_2023_);
v___x_2025_ = lean_nat_dec_le(v___x_2021_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_inc(v___x_2024_);
v___y_2011_ = v___x_2024_;
v___y_2012_ = v___x_2020_;
v___y_2013_ = v___x_2019_;
v___y_2014_ = v___x_2024_;
goto v___jp_2010_;
}
else
{
v___y_2011_ = v___x_2024_;
v___y_2012_ = v___x_2020_;
v___y_2013_ = v___x_2019_;
v___y_2014_ = v___x_2021_;
goto v___jp_2010_;
}
}
else
{
lean_dec_ref(v___f_1997_);
v___y_2001_ = v___x_2019_;
goto v___jp_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2028_, lean_object* v_toEnvExtension_2029_, lean_object* v_env_2030_, lean_object* v_asyncMode_2031_, lean_object* v___x_2032_, uint8_t v___x_2033_, lean_object* v_inst_2034_, lean_object* v___f_2035_, lean_object* v_toBind_2036_, lean_object* v___f_2037_, lean_object* v_____s_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v_importedEntries_2040_; size_t v_sz_2041_; size_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2039_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2028_, v_toEnvExtension_2029_, v_env_2030_, v_asyncMode_2031_, v___x_2032_, v___x_2033_);
v_importedEntries_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_ref(v_importedEntries_2040_);
lean_dec(v___x_2039_);
v_sz_2041_ = lean_array_size(v_importedEntries_2040_);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2034_, v_importedEntries_2040_, v___f_2035_, v_sz_2041_, v___x_2042_, v_____s_2038_);
v___x_2044_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v___x_2043_, v___f_2037_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2045_, lean_object* v_toEnvExtension_2046_, lean_object* v_env_2047_, lean_object* v_asyncMode_2048_, lean_object* v___x_2049_, lean_object* v___x_2050_, lean_object* v_inst_2051_, lean_object* v___f_2052_, lean_object* v_toBind_2053_, lean_object* v___f_2054_, lean_object* v_____s_2055_){
_start:
{
uint8_t v___x_532__boxed_2056_; lean_object* v_res_2057_; 
v___x_532__boxed_2056_ = lean_unbox(v___x_2050_);
v_res_2057_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2045_, v_toEnvExtension_2046_, v_env_2047_, v_asyncMode_2048_, v___x_2049_, v___x_532__boxed_2056_, v_inst_2051_, v___f_2052_, v_toBind_2053_, v___f_2054_, v_____s_2055_);
lean_dec(v_asyncMode_2048_);
lean_dec_ref(v_toEnvExtension_2046_);
lean_dec_ref(v___x_2045_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2058_, lean_object* v_inst_2059_, lean_object* v___f_2060_, lean_object* v_toBind_2061_, lean_object* v___f_2062_, lean_object* v___x_2063_, lean_object* v___f_2064_, lean_object* v___f_2065_, lean_object* v_env_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v_toEnvExtension_2068_; lean_object* v_asyncMode_2069_; lean_object* v_found_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2067_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2068_ = lean_ctor_get(v___x_2067_, 0);
v_asyncMode_2069_ = lean_ctor_get(v_toEnvExtension_2068_, 2);
v_found_2070_ = l_Lean_NameSet_empty;
v___x_2071_ = lean_box(0);
v___x_2072_ = 0;
v___x_2073_ = lean_box(v___x_2072_);
lean_inc_n(v_toBind_2061_, 2);
lean_inc_ref(v_inst_2059_);
lean_inc(v_asyncMode_2069_);
lean_inc_ref(v_env_2066_);
lean_inc_ref(v_toEnvExtension_2068_);
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_2074_, 0, v___x_2058_);
lean_closure_set(v___f_2074_, 1, v_toEnvExtension_2068_);
lean_closure_set(v___f_2074_, 2, v_env_2066_);
lean_closure_set(v___f_2074_, 3, v_asyncMode_2069_);
lean_closure_set(v___f_2074_, 4, v___x_2071_);
lean_closure_set(v___f_2074_, 5, v___x_2073_);
lean_closure_set(v___f_2074_, 6, v_inst_2059_);
lean_closure_set(v___f_2074_, 7, v___f_2060_);
lean_closure_set(v___f_2074_, 8, v_toBind_2061_);
lean_closure_set(v___f_2074_, 9, v___f_2062_);
v___x_2075_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2063_, v___x_2067_, v_env_2066_, v_asyncMode_2069_, v___x_2071_, v___x_2072_);
v___x_2076_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2059_, v___f_2064_, v_found_2070_, v___x_2075_);
v___x_2077_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2076_, v___f_2065_);
v___x_2078_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2077_, v___f_2074_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2081_, lean_object* v_inst_2082_){
_start:
{
lean_object* v_toApplicative_2083_; lean_object* v_toBind_2084_; lean_object* v_getEnv_2085_; lean_object* v_toPure_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; 
v_toApplicative_2083_ = lean_ctor_get(v_inst_2081_, 0);
v_toBind_2084_ = lean_ctor_get(v_inst_2081_, 1);
lean_inc_n(v_toBind_2084_, 3);
v_getEnv_2085_ = lean_ctor_get(v_inst_2082_, 0);
lean_inc(v_getEnv_2085_);
lean_dec_ref(v_inst_2082_);
v_toPure_2086_ = lean_ctor_get(v_toApplicative_2083_, 1);
v___f_2087_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2088_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2089_ = lean_box(1);
v___x_2090_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_2086_, 5);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2091_, 0, v_toPure_2086_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2092_, 0, v_toPure_2086_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2093_, 0, v_toPure_2086_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2094_, 0, v_toPure_2086_);
lean_inc_ref(v_inst_2081_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2095_, 0, v_inst_2081_);
lean_closure_set(v___f_2095_, 1, v___f_2093_);
lean_closure_set(v___f_2095_, 2, v_toBind_2084_);
lean_closure_set(v___f_2095_, 3, v___f_2094_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2096_, 0, v_toPure_2086_);
lean_closure_set(v___f_2096_, 1, v___f_2088_);
lean_closure_set(v___f_2096_, 2, v___f_2087_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2097_, 0, v___x_2090_);
lean_closure_set(v___f_2097_, 1, v_inst_2081_);
lean_closure_set(v___f_2097_, 2, v___f_2095_);
lean_closure_set(v___f_2097_, 3, v_toBind_2084_);
lean_closure_set(v___f_2097_, 4, v___f_2096_);
lean_closure_set(v___f_2097_, 5, v___x_2089_);
lean_closure_set(v___f_2097_, 6, v___f_2092_);
lean_closure_set(v___f_2097_, 7, v___f_2091_);
v___x_2098_ = lean_apply_4(v_toBind_2084_, lean_box(0), lean_box(0), v_getEnv_2085_, v___f_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2100_, v_inst_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2103_, lean_object* v_k_2104_, lean_object* v_v_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_k_2104_);
lean_ctor_set(v___x_2106_, 1, v_v_2105_);
v___x_2107_ = lean_array_push(v_arr_2103_, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2108_, lean_object* v_x2_2109_){
_start:
{
lean_object* v_fst_2110_; lean_object* v_fst_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_fst_2110_ = lean_ctor_get(v_x1_2108_, 0);
lean_inc(v_fst_2110_);
lean_dec_ref(v_x1_2108_);
v_fst_2111_ = lean_ctor_get(v_x2_2109_, 0);
lean_inc(v_fst_2111_);
lean_dec_ref(v_x2_2109_);
v___x_2112_ = 1;
v___x_2113_ = l_Lean_Name_toString(v_fst_2110_, v___x_2112_);
v___x_2114_ = l_Lean_Name_toString(v_fst_2111_, v___x_2112_);
v___x_2115_ = lean_string_dec_lt(v___x_2113_, v___x_2114_);
lean_dec_ref(v___x_2114_);
lean_dec_ref(v___x_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2116_, lean_object* v_x2_2117_){
_start:
{
uint8_t v_res_2118_; lean_object* v_r_2119_; 
v_res_2118_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2116_, v_x2_2117_);
v_r_2119_ = lean_box(v_res_2118_);
return v_r_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2120_, lean_object* v_a_2121_, lean_object* v_b_2122_, lean_object* v_c_2123_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2121_, v_b_2122_, v_c_2123_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
v___x_2126_ = lean_apply_2(v_toPure_2120_, lean_box(0), v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2127_, lean_object* v_a_2128_, lean_object* v_x_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_fst_2131_; lean_object* v_snd_2132_; lean_object* v_found_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_fst_2131_ = lean_ctor_get(v_a_2128_, 0);
lean_inc(v_fst_2131_);
v_snd_2132_ = lean_ctor_get(v_a_2128_, 1);
lean_inc(v_snd_2132_);
lean_dec_ref(v_a_2128_);
v_found_2133_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2131_, v_snd_2132_, v___y_2130_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_found_2133_);
v___x_2135_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2136_, lean_object* v___f_2137_, lean_object* v___f_2138_, lean_object* v_____s_2139_){
_start:
{
lean_object* v___y_2141_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_arr_2146_; lean_object* v___x_2147_; lean_object* v___y_2149_; lean_object* v___y_2150_; uint8_t v___x_2152_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2146_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2137_, v___x_2145_, v_____s_2139_);
v___x_2147_ = lean_array_get_size(v_arr_2146_);
v___x_2152_ = lean_nat_dec_eq(v___x_2147_, v___x_2144_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___y_2156_; uint8_t v___x_2158_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v___x_2147_, v___x_2153_);
v___x_2158_ = lean_nat_dec_le(v___x_2144_, v___x_2154_);
if (v___x_2158_ == 0)
{
lean_inc(v___x_2154_);
v___y_2156_ = v___x_2154_;
goto v___jp_2155_;
}
else
{
v___y_2156_ = v___x_2144_;
goto v___jp_2155_;
}
v___jp_2155_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_nat_dec_le(v___y_2156_, v___x_2154_);
if (v___x_2157_ == 0)
{
lean_dec(v___x_2154_);
lean_inc(v___y_2156_);
v___y_2149_ = v___y_2156_;
v___y_2150_ = v___y_2156_;
goto v___jp_2148_;
}
else
{
v___y_2149_ = v___y_2156_;
v___y_2150_ = v___x_2154_;
goto v___jp_2148_;
}
}
}
else
{
lean_dec_ref(v___f_2138_);
v___y_2141_ = v_arr_2146_;
goto v___jp_2140_;
}
v___jp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_array_to_list(v___y_2141_);
v___x_2143_ = lean_apply_2(v_toPure_2136_, lean_box(0), v___x_2142_);
return v___x_2143_;
}
v___jp_2148_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2138_, v___x_2147_, v_arr_2146_, v___y_2149_, v___y_2150_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2150_);
v___y_2141_ = v___x_2151_;
goto v___jp_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2159_, lean_object* v_inst_2160_, lean_object* v___f_2161_, lean_object* v_toBind_2162_, lean_object* v___f_2163_, lean_object* v___x_2164_, lean_object* v___f_2165_, lean_object* v___f_2166_, lean_object* v_env_2167_){
_start:
{
lean_object* v___x_2168_; lean_object* v_toEnvExtension_2169_; lean_object* v_asyncMode_2170_; lean_object* v_found_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2168_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2169_ = lean_ctor_get(v___x_2168_, 0);
v_asyncMode_2170_ = lean_ctor_get(v_toEnvExtension_2169_, 2);
v_found_2171_ = lean_box(1);
v___x_2172_ = lean_box(0);
v___x_2173_ = 0;
v___x_2174_ = lean_box(v___x_2173_);
lean_inc_n(v_toBind_2162_, 2);
lean_inc_ref(v_inst_2160_);
lean_inc(v_asyncMode_2170_);
lean_inc_ref(v_env_2167_);
lean_inc_ref(v_toEnvExtension_2169_);
v___f_2175_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_2175_, 0, v___x_2159_);
lean_closure_set(v___f_2175_, 1, v_toEnvExtension_2169_);
lean_closure_set(v___f_2175_, 2, v_env_2167_);
lean_closure_set(v___f_2175_, 3, v_asyncMode_2170_);
lean_closure_set(v___f_2175_, 4, v___x_2172_);
lean_closure_set(v___f_2175_, 5, v___x_2174_);
lean_closure_set(v___f_2175_, 6, v_inst_2160_);
lean_closure_set(v___f_2175_, 7, v___f_2161_);
lean_closure_set(v___f_2175_, 8, v_toBind_2162_);
lean_closure_set(v___f_2175_, 9, v___f_2163_);
v___x_2176_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2164_, v___x_2168_, v_env_2167_, v_asyncMode_2170_, v___x_2172_, v___x_2173_);
v___x_2177_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2160_, v___f_2165_, v_found_2171_, v___x_2176_);
v___x_2178_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v___x_2177_, v___f_2166_);
v___x_2179_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v___x_2178_, v___f_2175_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2182_, lean_object* v_inst_2183_){
_start:
{
lean_object* v_toApplicative_2184_; lean_object* v_toBind_2185_; lean_object* v_getEnv_2186_; lean_object* v_toPure_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_toApplicative_2184_ = lean_ctor_get(v_inst_2182_, 0);
v_toBind_2185_ = lean_ctor_get(v_inst_2182_, 1);
lean_inc_n(v_toBind_2185_, 3);
v_getEnv_2186_ = lean_ctor_get(v_inst_2183_, 0);
lean_inc(v_getEnv_2186_);
lean_dec_ref(v_inst_2183_);
v_toPure_2187_ = lean_ctor_get(v_toApplicative_2184_, 1);
v___f_2188_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2189_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2190_ = lean_box(1);
v___x_2191_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_2187_, 5);
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2192_, 0, v_toPure_2187_);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2187_);
v___f_2194_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2194_, 0, v_toPure_2187_);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2195_, 0, v_toPure_2187_);
lean_inc_ref(v_inst_2182_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2196_, 0, v_inst_2182_);
lean_closure_set(v___f_2196_, 1, v___f_2194_);
lean_closure_set(v___f_2196_, 2, v_toBind_2185_);
lean_closure_set(v___f_2196_, 3, v___f_2195_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2197_, 0, v_toPure_2187_);
lean_closure_set(v___f_2197_, 1, v___f_2188_);
lean_closure_set(v___f_2197_, 2, v___f_2189_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2198_, 0, v___x_2191_);
lean_closure_set(v___f_2198_, 1, v_inst_2182_);
lean_closure_set(v___f_2198_, 2, v___f_2196_);
lean_closure_set(v___f_2198_, 3, v_toBind_2185_);
lean_closure_set(v___f_2198_, 4, v___f_2197_);
lean_closure_set(v___f_2198_, 5, v___x_2190_);
lean_closure_set(v___f_2198_, 6, v___f_2193_);
lean_closure_set(v___f_2198_, 7, v___f_2192_);
v___x_2199_ = lean_apply_4(v_toBind_2185_, lean_box(0), lean_box(0), v_getEnv_2186_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2201_, v_inst_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2204_, lean_object* v_init_2205_, lean_object* v_x_2206_){
_start:
{
if (lean_obj_tag(v_x_2206_) == 0)
{
lean_object* v_k_2207_; lean_object* v_l_2208_; lean_object* v_r_2209_; lean_object* v___x_2210_; lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_k_2207_ = lean_ctor_get(v_x_2206_, 1);
v_l_2208_ = lean_ctor_get(v_x_2206_, 3);
v_r_2209_ = lean_ctor_get(v_x_2206_, 4);
lean_inc_n(v_a_2204_, 2);
v___x_2210_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2204_, v_init_2205_, v_l_2208_);
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
lean_inc(v_k_2207_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2204_);
lean_ctor_set(v___x_2212_, 1, v_k_2207_);
v___x_2213_ = lean_array_push(v_a_2211_, v___x_2212_);
v_init_2205_ = v___x_2213_;
v_x_2206_ = v_r_2209_;
goto _start;
}
else
{
lean_object* v___x_2215_; 
lean_dec(v_a_2204_);
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_init_2205_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2216_, lean_object* v_init_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2216_, v_init_2217_, v_x_2218_);
lean_dec(v_x_2218_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2220_, lean_object* v_x_2221_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v_l_2224_; lean_object* v_r_2225_; lean_object* v___x_2226_; lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v_a_2229_; 
v_k_2222_ = lean_ctor_get(v_x_2221_, 1);
lean_inc(v_k_2222_);
v_v_2223_ = lean_ctor_get(v_x_2221_, 2);
lean_inc(v_v_2223_);
v_l_2224_ = lean_ctor_get(v_x_2221_, 3);
lean_inc(v_l_2224_);
v_r_2225_ = lean_ctor_get(v_x_2221_, 4);
lean_inc(v_r_2225_);
lean_dec_ref_known(v_x_2221_, 5);
v___x_2226_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2220_, v_l_2224_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2222_, v_a_2227_, v_v_2223_);
lean_dec(v_v_2223_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref(v___x_2228_);
v_init_2220_ = v_a_2229_;
v_x_2221_ = v_r_2225_;
goto _start;
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_init_2220_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2232_){
_start:
{
lean_object* v_exported_2233_; lean_object* v___x_2234_; lean_object* v_a_2235_; 
v_exported_2233_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2233_, v_tags_2232_);
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2234_);
return v_a_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2236_, lean_object* v_s_2237_){
_start:
{
lean_object* v_exported_2238_; lean_object* v___x_2239_; lean_object* v_a_2240_; lean_object* v___x_2241_; 
v_exported_2238_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2238_, v_s_2237_);
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_n(v_a_2240_, 3);
lean_dec_ref(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2240_);
lean_ctor_set(v___x_2241_, 1, v_a_2240_);
lean_ctor_set(v___x_2241_, 2, v_a_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2242_, lean_object* v_s_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2242_, v_s_2243_);
lean_dec_ref(v_x_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2245_, lean_object* v_k_2246_, lean_object* v_fallback_2247_){
_start:
{
if (lean_obj_tag(v_t_2245_) == 0)
{
lean_object* v_k_2248_; lean_object* v_v_2249_; lean_object* v_l_2250_; lean_object* v_r_2251_; uint8_t v___x_2252_; 
v_k_2248_ = lean_ctor_get(v_t_2245_, 1);
v_v_2249_ = lean_ctor_get(v_t_2245_, 2);
v_l_2250_ = lean_ctor_get(v_t_2245_, 3);
v_r_2251_ = lean_ctor_get(v_t_2245_, 4);
v___x_2252_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2246_, v_k_2248_);
switch(v___x_2252_)
{
case 0:
{
v_t_2245_ = v_l_2250_;
goto _start;
}
case 1:
{
lean_inc(v_v_2249_);
return v_v_2249_;
}
default: 
{
v_t_2245_ = v_r_2251_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2247_);
return v_fallback_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2255_, lean_object* v_k_2256_, lean_object* v_fallback_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2255_, v_k_2256_, v_fallback_2257_);
lean_dec(v_fallback_2257_);
lean_dec(v_k_2256_);
lean_dec(v_t_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v_fst_2261_; lean_object* v_snd_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_fst_2261_ = lean_ctor_get(v_x_2260_, 0);
lean_inc(v_fst_2261_);
v_snd_2262_ = lean_ctor_get(v_x_2260_, 1);
lean_inc(v_snd_2262_);
lean_dec_ref(v_x_2260_);
v___x_2263_ = l_Lean_NameSet_empty;
v___x_2264_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2259_, v_fst_2261_, v___x_2263_);
v___x_2265_ = l_Lean_NameSet_insert(v___x_2264_, v_snd_2262_);
v___x_2266_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2261_, v___x_2265_, v_tags_2259_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2292_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2295_, lean_object* v_t_2296_, lean_object* v_k_2297_, lean_object* v_fallback_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2296_, v_k_2297_, v_fallback_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2300_, lean_object* v_t_2301_, lean_object* v_k_2302_, lean_object* v_fallback_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2300_, v_t_2301_, v_k_2302_, v_fallback_2303_);
lean_dec(v_fallback_2303_);
lean_dec(v_k_2302_);
lean_dec(v_t_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
if (lean_obj_tag(v_a_2305_) == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = l_List_reverse___redArg(v_a_2306_);
return v___x_2307_;
}
else
{
lean_object* v_head_2308_; lean_object* v_tail_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2321_; 
v_head_2308_ = lean_ctor_get(v_a_2305_, 0);
v_tail_2309_ = lean_ctor_get(v_a_2305_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2305_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2311_ = v_a_2305_;
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_tail_2309_);
lean_inc(v_head_2308_);
lean_dec(v_a_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2321_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2313_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2314_ = l_Lean_MessageData_ofName(v_head_2308_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2313_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v_a_2306_);
lean_ctor_set(v___x_2311_, 0, v___x_2316_);
v___x_2318_ = v___x_2311_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2306_);
v___x_2318_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
v_a_2305_ = v_tail_2309_;
v_a_2306_ = v___x_2318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___lam__0(lean_object* v_addEntryFn_2322_, lean_object* v___x_2323_, lean_object* v_s_2324_){
_start:
{
lean_object* v_importedEntries_2325_; lean_object* v_state_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_importedEntries_2325_ = lean_ctor_get(v_s_2324_, 0);
v_state_2326_ = lean_ctor_get(v_s_2324_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_s_2324_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_s_2324_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_state_2326_);
lean_inc(v_importedEntries_2325_);
lean_dec(v_s_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_state_2330_; lean_object* v___x_2332_; 
v_state_2330_ = lean_apply_2(v_addEntryFn_2322_, v_state_2326_, v___x_2323_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v_state_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_importedEntries_2325_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_state_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2335_, lean_object* v_k_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v_m_2341_; lean_object* v_a_2342_; uint8_t v___x_2343_; 
v___x_2339_ = lean_nat_add(v_x_2337_, v_x_2338_);
v___x_2340_ = lean_unsigned_to_nat(1u);
v_m_2341_ = lean_nat_shiftr(v___x_2339_, v___x_2340_);
lean_dec(v___x_2339_);
v_a_2342_ = lean_array_fget_borrowed(v_as_2335_, v_m_2341_);
v___x_2343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2342_, v_k_2336_);
if (v___x_2343_ == 0)
{
uint8_t v___x_2344_; 
lean_dec(v_x_2338_);
v___x_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2336_, v_a_2342_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_m_2341_);
lean_dec(v_x_2337_);
lean_inc(v_a_2342_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_a_2342_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_nat_dec_eq(v_m_2341_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_nat_sub(v_m_2341_, v___x_2340_);
lean_dec(v_m_2341_);
v___x_2349_ = lean_nat_dec_lt(v___x_2348_, v_x_2337_);
if (v___x_2349_ == 0)
{
v_x_2338_ = v___x_2348_;
goto _start;
}
else
{
lean_object* v___x_2351_; 
lean_dec(v___x_2348_);
lean_dec(v_x_2337_);
v___x_2351_ = lean_box(0);
return v___x_2351_;
}
}
else
{
lean_object* v___x_2352_; 
lean_dec(v_m_2341_);
lean_dec(v_x_2337_);
v___x_2352_ = lean_box(0);
return v___x_2352_;
}
}
}
else
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
lean_dec(v_x_2337_);
v___x_2353_ = lean_nat_add(v_m_2341_, v___x_2340_);
lean_dec(v_m_2341_);
v___x_2354_ = lean_nat_dec_le(v___x_2353_, v_x_2338_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec(v___x_2353_);
lean_dec(v_x_2338_);
v___x_2355_ = lean_box(0);
return v___x_2355_;
}
else
{
v_x_2337_ = v___x_2353_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2357_, lean_object* v_k_2358_, lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2357_, v_k_2358_, v_x_2359_, v_x_2360_);
lean_dec_ref(v_k_2358_);
lean_dec_ref(v_as_2357_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v_env_2370_; lean_object* v___x_2371_; 
v___x_2365_ = lean_box(1);
v___x_2366_ = lean_st_ref_get(v___y_2363_);
v_env_2370_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_env_2370_);
lean_dec(v___x_2366_);
v___x_2371_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2370_, v_tag_2362_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; lean_object* v_toEnvExtension_2373_; lean_object* v_asyncMode_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2372_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2373_ = lean_ctor_get(v___x_2372_, 0);
v_asyncMode_2374_ = lean_ctor_get(v_toEnvExtension_2373_, 2);
v___x_2375_ = lean_box(0);
v___x_2376_ = 0;
v___x_2377_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2365_, v___x_2372_, v_env_2370_, v_asyncMode_2374_, v___x_2375_, v___x_2376_);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2377_, v_tag_2362_);
lean_dec(v_tag_2362_);
lean_dec(v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2408_; 
v_val_2380_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2382_ = v___x_2371_;
v_isShared_2383_ = v_isSharedCheck_2408_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v___x_2371_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2408_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2384_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2385_ = 0;
v___x_2386_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2365_, v___x_2384_, v_env_2370_, v_val_2380_, v___x_2385_);
lean_dec(v_val_2380_);
lean_dec_ref(v_env_2370_);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_array_get_size(v___x_2386_);
v___x_2389_ = lean_nat_dec_lt(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_dec_ref(v___x_2386_);
lean_del_object(v___x_2382_);
lean_dec(v_tag_2362_);
goto v___jp_2367_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(1u);
v___x_2391_ = lean_nat_sub(v___x_2388_, v___x_2390_);
v___x_2392_ = lean_nat_dec_le(v___x_2387_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_dec(v___x_2391_);
lean_dec_ref(v___x_2386_);
lean_del_object(v___x_2382_);
lean_dec(v_tag_2362_);
goto v___jp_2367_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_tag_2362_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2386_, v___x_2394_, v___x_2387_, v___x_2391_);
lean_dec_ref_known(v___x_2394_, 2);
lean_dec_ref(v___x_2386_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_del_object(v___x_2382_);
goto v___jp_2367_;
}
else
{
lean_object* v_val_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2407_; 
v_val_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_val_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_snd_2400_; lean_object* v___x_2402_; 
v_snd_2400_ = lean_ctor_get(v_val_2396_, 1);
lean_inc(v_snd_2400_);
lean_dec(v_val_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v_snd_2400_);
v___x_2402_ = v___x_2398_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_snd_2400_);
v___x_2402_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2402_);
v___x_2404_ = v___x_2382_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2409_, v___y_2410_);
lean_dec(v___y_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2413_, size_t v_sz_2414_, size_t v_i_2415_, lean_object* v_b_2416_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_lt(v_i_2415_, v_sz_2414_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_b_2416_);
return v___x_2419_;
}
else
{
lean_object* v_a_2420_; lean_object* v_fst_2421_; lean_object* v_found_2422_; size_t v___x_2423_; size_t v___x_2424_; 
v_a_2420_ = lean_array_uget_borrowed(v_as_2413_, v_i_2415_);
v_fst_2421_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_fst_2421_);
v_found_2422_ = l_Lean_NameSet_insert(v_b_2416_, v_fst_2421_);
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_add(v_i_2415_, v___x_2423_);
v_i_2415_ = v___x_2424_;
v_b_2416_ = v_found_2422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2426_, lean_object* v_sz_2427_, lean_object* v_i_2428_, lean_object* v_b_2429_, lean_object* v___y_2430_){
_start:
{
size_t v_sz_boxed_2431_; size_t v_i_boxed_2432_; lean_object* v_res_2433_; 
v_sz_boxed_2431_ = lean_unbox_usize(v_sz_2427_);
lean_dec(v_sz_2427_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2428_);
lean_dec(v_i_2428_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2426_, v_sz_boxed_2431_, v_i_boxed_2432_, v_b_2429_);
lean_dec_ref(v_as_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_b_2437_);
return v___x_2442_;
}
else
{
lean_object* v_a_2443_; size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_a_2443_ = lean_array_uget_borrowed(v_as_2434_, v_i_2436_);
v_sz_2444_ = lean_array_size(v_a_2443_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2443_, v_sz_2444_, v___x_2445_, v_b_2437_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; size_t v___x_2448_; size_t v___x_2449_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_add(v_i_2436_, v___x_2448_);
v_i_2436_ = v___x_2449_;
v_b_2437_ = v_a_2447_;
goto _start;
}
else
{
return v___x_2446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2451_, lean_object* v_sz_2452_, lean_object* v_i_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2452_);
lean_dec(v_sz_2452_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2451_, v_sz_boxed_2458_, v_i_boxed_2459_, v_b_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec_ref(v_as_2451_);
return v_res_2460_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2461_, lean_object* v_x1_2462_, lean_object* v_x2_2463_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2464_ = l_Lean_Name_toString(v_x1_2462_, v___x_2461_);
v___x_2465_ = l_Lean_Name_toString(v_x2_2463_, v___x_2461_);
v___x_2466_ = lean_string_dec_lt(v___x_2464_, v___x_2465_);
lean_dec_ref(v___x_2465_);
lean_dec_ref(v___x_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2467_, lean_object* v_x1_2468_, lean_object* v_x2_2469_){
_start:
{
uint8_t v___x_6897__boxed_2470_; uint8_t v_res_2471_; lean_object* v_r_2472_; 
v___x_6897__boxed_2470_ = lean_unbox(v___x_2467_);
v_res_2471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_6897__boxed_2470_, v_x1_2468_, v_x2_2469_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object* v_hi_2473_, lean_object* v_pivot_2474_, lean_object* v_as_2475_, lean_object* v_i_2476_, lean_object* v_k_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_lt(v_k_2477_, v_hi_2473_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_k_2477_);
lean_dec(v_pivot_2474_);
v___x_2479_ = lean_array_fswap(v_as_2475_, v_i_2476_, v_hi_2473_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_i_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2481_ = lean_array_fget_borrowed(v_as_2475_, v_k_2477_);
lean_inc(v___x_2481_);
v___x_2482_ = l_Lean_Name_toString(v___x_2481_, v___x_2478_);
lean_inc(v_pivot_2474_);
v___x_2483_ = l_Lean_Name_toString(v_pivot_2474_, v___x_2478_);
v___x_2484_ = lean_string_dec_lt(v___x_2482_, v___x_2483_);
lean_dec_ref(v___x_2483_);
lean_dec_ref(v___x_2482_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_unsigned_to_nat(1u);
v___x_2486_ = lean_nat_add(v_k_2477_, v___x_2485_);
lean_dec(v_k_2477_);
v_k_2477_ = v___x_2486_;
goto _start;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2488_ = lean_array_fswap(v_as_2475_, v_i_2476_, v_k_2477_);
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_nat_add(v_i_2476_, v___x_2489_);
lean_dec(v_i_2476_);
v___x_2491_ = lean_nat_add(v_k_2477_, v___x_2489_);
lean_dec(v_k_2477_);
v_as_2475_ = v___x_2488_;
v_i_2476_ = v___x_2490_;
v_k_2477_ = v___x_2491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_hi_2493_, lean_object* v_pivot_2494_, lean_object* v_as_2495_, lean_object* v_i_2496_, lean_object* v_k_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2493_, v_pivot_2494_, v_as_2495_, v_i_2496_, v_k_2497_);
lean_dec(v_hi_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_n_2499_, lean_object* v_as_2500_, lean_object* v_lo_2501_, lean_object* v_hi_2502_){
_start:
{
lean_object* v___y_2504_; uint8_t v___x_2514_; 
v___x_2514_ = lean_nat_dec_lt(v_lo_2501_, v_hi_2502_);
if (v___x_2514_ == 0)
{
lean_dec(v_lo_2501_);
return v_as_2500_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v_mid_2517_; lean_object* v___y_2519_; lean_object* v___y_2525_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2515_ = lean_nat_add(v_lo_2501_, v_hi_2502_);
v___x_2516_ = lean_unsigned_to_nat(1u);
v_mid_2517_ = lean_nat_shiftr(v___x_2515_, v___x_2516_);
lean_dec(v___x_2515_);
v___x_2530_ = lean_array_fget_borrowed(v_as_2500_, v_mid_2517_);
v___x_2531_ = lean_array_fget_borrowed(v_as_2500_, v_lo_2501_);
lean_inc(v___x_2531_);
lean_inc(v___x_2530_);
v___x_2532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2514_, v___x_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
v___y_2525_ = v_as_2500_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_array_fswap(v_as_2500_, v_lo_2501_, v_mid_2517_);
v___y_2525_ = v___x_2533_;
goto v___jp_2524_;
}
v___jp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2520_ = lean_array_fget_borrowed(v___y_2519_, v_mid_2517_);
v___x_2521_ = lean_array_fget_borrowed(v___y_2519_, v_hi_2502_);
lean_inc(v___x_2521_);
lean_inc(v___x_2520_);
v___x_2522_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2514_, v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec(v_mid_2517_);
v___y_2504_ = v___y_2519_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_array_fswap(v___y_2519_, v_mid_2517_, v_hi_2502_);
lean_dec(v_mid_2517_);
v___y_2504_ = v___x_2523_;
goto v___jp_2503_;
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2526_ = lean_array_fget_borrowed(v___y_2525_, v_hi_2502_);
v___x_2527_ = lean_array_fget_borrowed(v___y_2525_, v_lo_2501_);
lean_inc(v___x_2527_);
lean_inc(v___x_2526_);
v___x_2528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2514_, v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
v___y_2519_ = v___y_2525_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_array_fswap(v___y_2525_, v_lo_2501_, v_hi_2502_);
v___y_2519_ = v___x_2529_;
goto v___jp_2518_;
}
}
}
v___jp_2503_:
{
lean_object* v_pivot_2505_; lean_object* v___x_2506_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; uint8_t v___x_2509_; 
v_pivot_2505_ = lean_array_fget(v___y_2504_, v_hi_2502_);
lean_inc_n(v_lo_2501_, 2);
v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2502_, v_pivot_2505_, v___y_2504_, v_lo_2501_, v_lo_2501_);
v_fst_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_fst_2507_);
v_snd_2508_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_snd_2508_);
lean_dec_ref(v___x_2506_);
v___x_2509_ = lean_nat_dec_le(v_hi_2502_, v_fst_2507_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2499_, v_snd_2508_, v_lo_2501_, v_fst_2507_);
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_nat_add(v_fst_2507_, v___x_2511_);
lean_dec(v_fst_2507_);
v_as_2500_ = v___x_2510_;
v_lo_2501_ = v___x_2512_;
goto _start;
}
else
{
lean_dec(v_fst_2507_);
lean_dec(v_lo_2501_);
return v_snd_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_n_2534_, lean_object* v_as_2535_, lean_object* v_lo_2536_, lean_object* v_hi_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2534_, v_as_2535_, v_lo_2536_, v_hi_2537_);
lean_dec(v_hi_2537_);
lean_dec(v_n_2534_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2539_, lean_object* v_x_2540_){
_start:
{
if (lean_obj_tag(v_x_2540_) == 0)
{
lean_object* v_k_2542_; lean_object* v_l_2543_; lean_object* v_r_2544_; lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_k_2542_ = lean_ctor_get(v_x_2540_, 1);
lean_inc(v_k_2542_);
v_l_2543_ = lean_ctor_get(v_x_2540_, 3);
lean_inc(v_l_2543_);
v_r_2544_ = lean_ctor_get(v_x_2540_, 4);
lean_inc(v_r_2544_);
lean_dec_ref_known(v_x_2540_, 5);
v___x_2545_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2539_, v_l_2543_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v_a_2547_ = lean_ctor_get(v_a_2546_, 0);
lean_inc(v_a_2547_);
lean_dec(v_a_2546_);
v___x_2548_ = l_Lean_NameSet_insert(v_a_2547_, v_k_2542_);
v_init_2539_ = v___x_2548_;
v_x_2540_ = v_r_2544_;
goto _start;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_init_2539_);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2552_, v_x_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2556_, lean_object* v_x_2557_){
_start:
{
if (lean_obj_tag(v_x_2557_) == 0)
{
lean_object* v_k_2558_; lean_object* v_l_2559_; lean_object* v_r_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_k_2558_ = lean_ctor_get(v_x_2557_, 1);
lean_inc(v_k_2558_);
v_l_2559_ = lean_ctor_get(v_x_2557_, 3);
lean_inc(v_l_2559_);
v_r_2560_ = lean_ctor_get(v_x_2557_, 4);
lean_inc(v_r_2560_);
lean_dec_ref_known(v_x_2557_, 5);
v___x_2561_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2556_, v_l_2559_);
v___x_2562_ = lean_array_push(v___x_2561_, v_k_2558_);
v_init_2556_ = v___x_2562_;
v_x_2557_ = v_r_2560_;
goto _start;
}
else
{
return v_init_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___y_2568_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v_env_2597_; lean_object* v___x_2598_; lean_object* v_toEnvExtension_2599_; lean_object* v_asyncMode_2600_; lean_object* v_found_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v_a_2605_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_a_2624_; lean_object* v_a_2625_; 
v___x_2594_ = lean_box(1);
v___x_2595_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
v___x_2596_ = lean_st_ref_get(v___y_2565_);
v_env_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref_n(v_env_2597_, 2);
lean_dec(v___x_2596_);
v___x_2598_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2599_ = lean_ctor_get(v___x_2598_, 0);
v_asyncMode_2600_ = lean_ctor_get(v_toEnvExtension_2599_, 2);
v_found_2601_ = l_Lean_NameSet_empty;
v___x_2602_ = lean_box(0);
v___x_2603_ = 0;
v___x_2622_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2594_, v___x_2598_, v_env_2597_, v_asyncMode_2600_, v___x_2602_, v___x_2603_);
v___x_2623_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2601_, v___x_2622_);
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref(v___x_2623_);
v_a_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_a_2625_);
lean_dec(v_a_2624_);
v_a_2605_ = v_a_2625_;
goto v___jp_2604_;
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_array_to_list(v___y_2568_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
v___jp_2571_:
{
lean_object* v___x_2576_; 
v___x_2576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2573_, v___y_2574_, v___y_2572_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec(v___y_2573_);
v___y_2568_ = v___x_2576_;
goto v___jp_2567_;
}
v___jp_2577_:
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_le(v___y_2581_, v___y_2579_);
if (v___x_2582_ == 0)
{
lean_dec(v___y_2579_);
lean_inc(v___y_2581_);
v___y_2572_ = v___y_2581_;
v___y_2573_ = v___y_2578_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___y_2581_;
goto v___jp_2571_;
}
else
{
v___y_2572_ = v___y_2581_;
v___y_2573_ = v___y_2578_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___y_2579_;
goto v___jp_2571_;
}
}
v___jp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2586_ = lean_mk_empty_array_with_capacity(v___y_2585_);
lean_dec(v___y_2585_);
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2586_, v___y_2584_);
v___x_2588_ = lean_array_get_size(v___x_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_nat_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2591_ = lean_unsigned_to_nat(1u);
v___x_2592_ = lean_nat_sub(v___x_2588_, v___x_2591_);
v___x_2593_ = lean_nat_dec_le(v___x_2589_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_inc(v___x_2592_);
v___y_2578_ = v___x_2588_;
v___y_2579_ = v___x_2592_;
v___y_2580_ = v___x_2587_;
v___y_2581_ = v___x_2592_;
goto v___jp_2577_;
}
else
{
v___y_2578_ = v___x_2588_;
v___y_2579_ = v___x_2592_;
v___y_2580_ = v___x_2587_;
v___y_2581_ = v___x_2589_;
goto v___jp_2577_;
}
}
else
{
v___y_2568_ = v___x_2587_;
goto v___jp_2567_;
}
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v_importedEntries_2607_; size_t v_sz_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2606_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2595_, v_toEnvExtension_2599_, v_env_2597_, v_asyncMode_2600_, v___x_2602_, v___x_2603_);
v_importedEntries_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_importedEntries_2607_);
lean_dec(v___x_2606_);
v_sz_2608_ = lean_array_size(v_importedEntries_2607_);
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2607_, v_sz_2608_, v___x_2609_, v_a_2605_, v___y_2564_, v___y_2565_);
lean_dec_ref(v_importedEntries_2607_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v_size_2612_; 
v_size_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_size_2612_);
v___y_2584_ = v_a_2611_;
v___y_2585_ = v_size_2612_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_unsigned_to_nat(0u);
v___y_2584_ = v_a_2611_;
v___y_2585_ = v___x_2613_;
goto v___jp_2583_;
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2610_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2610_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2629_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2648_ = l_Lean_MessageData_ofFormat(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2653_ = l_Lean_MessageData_ofFormat(v___x_2652_);
return v___x_2653_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2656_ = l_Lean_stringToMessageData(v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2657_, uint8_t v___x_2658_, lean_object* v_as_2659_, size_t v_sz_2660_, size_t v_i_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_a_2667_; uint8_t v___x_2671_; 
v___x_2671_ = lean_usize_dec_lt(v_i_2661_, v_sz_2660_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec(v_decl_2657_);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_b_2662_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_unsigned_to_nat(1u);
v_a_2677_ = lean_array_uget_borrowed(v_as_2659_, v_i_2661_);
v___x_2678_ = l_Lean_TSyntax_getId(v_a_2677_);
lean_inc(v___x_2678_);
v___x_2679_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2678_, v___y_2664_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
if (lean_obj_tag(v_a_2680_) == 1)
{
lean_object* v___x_2681_; lean_object* v_env_2682_; lean_object* v_nextMacroScope_2683_; lean_object* v_ngen_2684_; lean_object* v_auxDeclNGen_2685_; lean_object* v_traceState_2686_; lean_object* v_recordedDeps_2687_; lean_object* v_messages_2688_; lean_object* v_infoState_2689_; lean_object* v_snapshotTasks_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref_known(v_a_2680_, 1);
v___x_2681_ = lean_st_ref_take(v___y_2664_);
v_env_2682_ = lean_ctor_get(v___x_2681_, 0);
v_nextMacroScope_2683_ = lean_ctor_get(v___x_2681_, 1);
v_ngen_2684_ = lean_ctor_get(v___x_2681_, 2);
v_auxDeclNGen_2685_ = lean_ctor_get(v___x_2681_, 3);
v_traceState_2686_ = lean_ctor_get(v___x_2681_, 4);
v_recordedDeps_2687_ = lean_ctor_get(v___x_2681_, 6);
v_messages_2688_ = lean_ctor_get(v___x_2681_, 7);
v_infoState_2689_ = lean_ctor_get(v___x_2681_, 8);
v_snapshotTasks_2690_ = lean_ctor_get(v___x_2681_, 9);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v___x_2681_, 5);
lean_dec(v_unused_2712_);
v___x_2692_ = v___x_2681_;
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_snapshotTasks_2690_);
lean_inc(v_infoState_2689_);
lean_inc(v_messages_2688_);
lean_inc(v_recordedDeps_2687_);
lean_inc(v_traceState_2686_);
lean_inc(v_auxDeclNGen_2685_);
lean_inc(v_ngen_2684_);
lean_inc(v_nextMacroScope_2683_);
lean_inc(v_env_2682_);
lean_dec(v___x_2681_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___y_2695_; lean_object* v___x_2701_; lean_object* v_toEnvExtension_2702_; lean_object* v_addEntryFn_2703_; lean_object* v_asyncMode_2704_; uint8_t v_logWrites_2705_; lean_object* v___x_2706_; lean_object* v___f_2707_; 
v___x_2701_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2702_ = lean_ctor_get(v___x_2701_, 0);
v_addEntryFn_2703_ = lean_ctor_get(v___x_2701_, 3);
v_asyncMode_2704_ = lean_ctor_get(v_toEnvExtension_2702_, 2);
v_logWrites_2705_ = lean_ctor_get_uint8(v_toEnvExtension_2702_, sizeof(void*)*6);
lean_inc(v_decl_2657_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_decl_2657_);
lean_ctor_set(v___x_2706_, 1, v___x_2678_);
lean_inc(v_addEntryFn_2703_);
v___f_2707_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2707_, 0, v_addEntryFn_2703_);
lean_closure_set(v___f_2707_, 1, v___x_2706_);
if (v_logWrites_2705_ == 0)
{
lean_object* v___x_2708_; 
lean_inc_ref(v_toEnvExtension_2702_);
v___x_2708_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2702_, v_env_2682_, v___f_2707_, v_asyncMode_2704_, v___x_2674_, v___x_2658_);
v___y_2695_ = v___x_2708_;
goto v___jp_2694_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_inc_ref_n(v_toEnvExtension_2702_, 2);
v___x_2709_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2702_, v_env_2682_);
lean_dec_ref(v_env_2682_);
v___x_2710_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2702_, v___x_2709_, v___f_2707_, v_asyncMode_2704_, v___x_2674_, v___x_2658_);
v___y_2695_ = v___x_2710_;
goto v___jp_2694_;
}
v___jp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 5, v___x_2696_);
lean_ctor_set(v___x_2692_, 0, v___y_2695_);
v___x_2698_ = v___x_2692_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___y_2695_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_nextMacroScope_2683_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_ngen_2684_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_auxDeclNGen_2685_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_traceState_2686_);
lean_ctor_set(v_reuseFailAlloc_2700_, 5, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2700_, 6, v_recordedDeps_2687_);
lean_ctor_set(v_reuseFailAlloc_2700_, 7, v_messages_2688_);
lean_ctor_set(v_reuseFailAlloc_2700_, 8, v_infoState_2689_);
lean_ctor_set(v_reuseFailAlloc_2700_, 9, v_snapshotTasks_2690_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_st_ref_put(v___y_2664_, v___x_2698_);
v_a_2667_ = v___x_2673_;
goto v___jp_2666_;
}
}
}
}
else
{
lean_object* v___x_2713_; 
lean_dec(v_a_2680_);
v___x_2713_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___y_2716_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2728_ = l_List_lengthTR___redArg(v_a_2714_);
v___x_2729_ = lean_nat_dec_eq(v___x_2728_, v___x_2675_);
if (v___x_2729_ == 0)
{
uint8_t v___x_2730_; 
v___x_2730_ = lean_nat_dec_eq(v___x_2728_, v___x_2676_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(10u);
v___x_2732_ = lean_nat_dec_lt(v___x_2728_, v___x_2731_);
lean_dec(v___x_2728_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_2714_);
v___x_2735_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_2714_, v_a_2714_, v___x_2731_, v___x_2734_);
lean_dec(v_a_2714_);
v___x_2736_ = lean_box(0);
v___x_2737_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_2735_, v___x_2736_);
v___x_2738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2739_ = l_Lean_MessageData_joinSep(v___x_2737_, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2733_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___y_2716_ = v___x_2742_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2714_, v___x_2744_);
v___x_2746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2747_ = l_Lean_MessageData_joinSep(v___x_2745_, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2743_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___y_2716_ = v___x_2748_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v___x_2728_);
v___x_2749_ = lean_box(0);
v___x_2750_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2714_, v___x_2749_);
v___x_2751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2752_ = l_Lean_MessageData_joinSep(v___x_2750_, v___x_2751_);
v___y_2716_ = v___x_2752_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2753_; 
lean_dec(v___x_2728_);
lean_dec(v_a_2714_);
v___x_2753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_2716_ = v___x_2753_;
goto v___jp_2715_;
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v___y_2716_);
v___x_2719_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_2722_ = l_Lean_MessageData_ofName(v___x_2678_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
lean_ctor_set(v___x_2726_, 1, v___x_2720_);
v___x_2727_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_a_2677_, v___x_2726_, v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_dec_ref_known(v___x_2727_, 1);
v_a_2667_ = v___x_2673_;
goto v___jp_2666_;
}
else
{
lean_dec(v_decl_2657_);
return v___x_2727_;
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v___x_2678_);
lean_dec(v_decl_2657_);
v_a_2754_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2713_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2713_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v___x_2678_);
lean_dec(v_decl_2657_);
v_a_2762_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2679_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2679_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
v___jp_2666_:
{
size_t v___x_2668_; size_t v___x_2669_; 
v___x_2668_ = ((size_t)1ULL);
v___x_2669_ = lean_usize_add(v_i_2661_, v___x_2668_);
v_i_2661_ = v___x_2669_;
v_b_2662_ = v_a_2667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_2770_, lean_object* v___x_2771_, lean_object* v_as_2772_, lean_object* v_sz_2773_, lean_object* v_i_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v___x_7245__boxed_2779_; size_t v_sz_boxed_2780_; size_t v_i_boxed_2781_; lean_object* v_res_2782_; 
v___x_7245__boxed_2779_ = lean_unbox(v___x_2771_);
v_sz_boxed_2780_ = lean_unbox_usize(v_sz_2773_);
lean_dec(v_sz_2773_);
v_i_boxed_2781_ = lean_unbox_usize(v_i_2774_);
lean_dec(v_i_2774_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2770_, v___x_7245__boxed_2779_, v_as_2772_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_as_2772_);
return v_res_2782_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_name_2789_, lean_object* v_decl_2790_, lean_object* v_stx_2791_, uint8_t v_kind_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; uint8_t v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = 0;
v___x_2859_ = l_Lean_instBEqAttributeKind_beq(v_kind_2792_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec(v_stx_2791_);
lean_dec(v_decl_2790_);
lean_dec_ref(v___x_2788_);
lean_dec_ref(v___x_2787_);
lean_dec_ref(v___x_2786_);
v___x_2860_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_2789_, v_kind_2792_, v___y_2793_, v___y_2794_);
return v___x_2860_;
}
else
{
goto v___jp_2832_;
}
v___jp_2796_:
{
lean_object* v___x_2801_; size_t v_sz_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = lean_box(0);
v_sz_2802_ = lean_array_size(v___y_2798_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2790_, v___y_2797_, v___y_2798_, v_sz_2802_, v___x_2803_, v___x_2801_, v___y_2799_, v___y_2800_);
lean_dec_ref(v___y_2798_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___x_2804_, 0);
lean_dec(v_unused_2812_);
v___x_2806_ = v___x_2804_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v___x_2804_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2801_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2801_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
return v___x_2804_;
}
}
v___jp_2813_:
{
lean_object* v___x_2818_; lean_object* v_env_2819_; lean_object* v___x_2820_; 
v___x_2818_ = lean_st_ref_get(v___y_2817_);
v_env_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc_ref(v_env_2819_);
lean_dec(v___x_2818_);
lean_inc(v_decl_2790_);
v___x_2820_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_2819_, v_decl_2790_);
if (lean_obj_tag(v___x_2820_) == 1)
{
lean_object* v_val_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v___y_2814_);
v_val_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_val_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2823_ = 0;
v___x_2824_ = l_Lean_MessageData_ofConstName(v_decl_2790_, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2822_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_MessageData_ofConstName(v_val_2821_, v___x_2823_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2822_);
v___x_2831_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_2791_, v___x_2830_, v___y_2816_, v___y_2817_);
lean_dec(v_stx_2791_);
return v___x_2831_;
}
else
{
lean_dec(v___x_2820_);
lean_dec(v_stx_2791_);
v___y_2797_ = v___y_2815_;
v___y_2798_ = v___y_2814_;
v___y_2799_ = v___y_2816_;
v___y_2800_ = v___y_2817_;
goto v___jp_2796_;
}
}
v___jp_2832_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_2834_ = l_Lean_Name_mkStr4(v___x_2786_, v___x_2787_, v___x_2833_, v___x_2788_);
lean_inc(v_stx_2791_);
v___x_2835_ = l_Lean_Syntax_isOfKind(v_stx_2791_, v___x_2834_);
lean_dec(v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec(v_stx_2791_);
lean_dec(v_decl_2790_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2837_ = l_Lean_MessageData_ofName(v_name_2789_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_2840_, v___y_2793_, v___y_2794_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_tags_2844_; lean_object* v___x_2845_; lean_object* v_env_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v_name_2789_);
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = l_Lean_Syntax_getArg(v_stx_2791_, v___x_2842_);
v_tags_2844_ = l_Lean_Syntax_getArgs(v___x_2843_);
lean_dec(v___x_2843_);
v___x_2845_ = lean_st_ref_get(v___y_2794_);
v_env_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2846_);
lean_dec(v___x_2845_);
v___x_2847_ = 0;
lean_inc(v_decl_2790_);
v___x_2848_ = l_Lean_Environment_find_x3f(v_env_2846_, v_decl_2790_, v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
v___y_2814_ = v_tags_2844_;
v___y_2815_ = v___x_2835_;
v___y_2816_ = v___y_2793_;
v___y_2817_ = v___y_2794_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2849_; lean_object* v_env_2850_; uint8_t v___x_2851_; 
lean_dec_ref_known(v___x_2848_, 1);
v___x_2849_ = lean_st_ref_get(v___y_2794_);
v_env_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc_ref(v_env_2850_);
lean_dec(v___x_2849_);
v___x_2851_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_2850_, v_decl_2790_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec_ref(v_tags_2844_);
v___x_2852_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_2853_ = l_Lean_MessageData_ofConstName(v_decl_2790_, v___x_2847_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_2791_, v___x_2856_, v___y_2793_, v___y_2794_);
lean_dec(v_stx_2791_);
return v___x_2857_;
}
else
{
v___y_2814_ = v_tags_2844_;
v___y_2815_ = v___x_2835_;
v___y_2816_ = v___y_2793_;
v___y_2817_ = v___y_2794_;
goto v___jp_2813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v_name_2864_, lean_object* v_decl_2865_, lean_object* v_stx_2866_, lean_object* v_kind_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
uint8_t v_kind_boxed_2871_; lean_object* v_res_2872_; 
v_kind_boxed_2871_ = lean_unbox(v_kind_2867_);
v_res_2872_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_2861_, v___x_2862_, v___x_2863_, v_name_2864_, v_decl_2865_, v_stx_2866_, v_kind_boxed_2871_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_2907_ = l_Lean_registerBuiltinAttribute(v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2910_, v___y_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_2920_, lean_object* v_k_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2920_, v_k_2921_, v_x_2922_, v_x_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_2926_, lean_object* v_k_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_2926_, v_k_2927_, v_x_2928_, v_x_2929_, v_x_2930_);
lean_dec_ref(v_k_2927_);
lean_dec_ref(v_as_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_2932_, size_t v_sz_2933_, size_t v_i_2934_, lean_object* v_b_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2932_, v_sz_2933_, v_i_2934_, v_b_2935_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_2940_, lean_object* v_sz_2941_, lean_object* v_i_2942_, lean_object* v_b_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2941_);
lean_dec(v_sz_2941_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2942_);
lean_dec(v_i_2942_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_2940_, v_sz_boxed_2947_, v_i_boxed_2948_, v_b_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_as_2940_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_2950_, lean_object* v_t_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2950_, v_t_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_2953_, lean_object* v_as_2954_, lean_object* v_lo_2955_, lean_object* v_hi_2956_, lean_object* v_w_2957_, lean_object* v_hlo_2958_, lean_object* v_hhi_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2953_, v_as_2954_, v_lo_2955_, v_hi_2956_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_2961_, lean_object* v_as_2962_, lean_object* v_lo_2963_, lean_object* v_hi_2964_, lean_object* v_w_2965_, lean_object* v_hlo_2966_, lean_object* v_hhi_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_2961_, v_as_2962_, v_lo_2963_, v_hi_2964_, v_w_2965_, v_hlo_2966_, v_hhi_2967_);
lean_dec(v_hi_2964_);
lean_dec(v_n_2961_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_2969_, lean_object* v_x_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2969_, v_x_2970_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_2975_, v_x_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object* v_n_2981_, lean_object* v_lo_2982_, lean_object* v_hi_2983_, lean_object* v_hhi_2984_, lean_object* v_pivot_2985_, lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_k_2988_, lean_object* v_ilo_2989_, lean_object* v_ik_2990_, lean_object* v_w_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2983_, v_pivot_2985_, v_as_2986_, v_i_2987_, v_k_2988_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object* v_n_2993_, lean_object* v_lo_2994_, lean_object* v_hi_2995_, lean_object* v_hhi_2996_, lean_object* v_pivot_2997_, lean_object* v_as_2998_, lean_object* v_i_2999_, lean_object* v_k_3000_, lean_object* v_ilo_3001_, lean_object* v_ik_3002_, lean_object* v_w_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(v_n_2993_, v_lo_2994_, v_hi_2995_, v_hhi_2996_, v_pivot_2997_, v_as_2998_, v_i_2999_, v_k_3000_, v_ilo_3001_, v_ik_3002_, v_w_3003_);
lean_dec(v_hi_2995_);
lean_dec(v_lo_2994_);
lean_dec(v_n_2993_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v_fst_3009_; lean_object* v_snd_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_fst_3009_ = lean_ctor_get(v_x_3008_, 0);
lean_inc(v_fst_3009_);
v_snd_3010_ = lean_ctor_get(v_x_3008_, 1);
lean_inc(v_snd_3010_);
lean_dec_ref(v_x_3008_);
v___x_3011_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3012_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3007_, v_fst_3009_, v___x_3011_);
v___x_3013_ = lean_array_push(v___x_3012_, v_snd_3010_);
v___x_3014_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3009_, v___x_3013_, v_es_3007_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3015_, lean_object* v_x_3016_){
_start:
{
if (lean_obj_tag(v_x_3016_) == 0)
{
lean_object* v_k_3017_; lean_object* v_v_3018_; lean_object* v_l_3019_; lean_object* v_r_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_k_3017_ = lean_ctor_get(v_x_3016_, 1);
v_v_3018_ = lean_ctor_get(v_x_3016_, 2);
v_l_3019_ = lean_ctor_get(v_x_3016_, 3);
v_r_3020_ = lean_ctor_get(v_x_3016_, 4);
v___x_3021_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3015_, v_l_3019_);
lean_inc(v_v_3018_);
lean_inc(v_k_3017_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_k_3017_);
lean_ctor_set(v___x_3022_, 1, v_v_3018_);
v___x_3023_ = lean_array_push(v___x_3021_, v___x_3022_);
v_init_3015_ = v___x_3023_;
v_x_3016_ = v_r_3020_;
goto _start;
}
else
{
return v_init_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3025_, v_x_3026_);
lean_dec(v_x_3026_);
return v_res_3027_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3028_, lean_object* v_x2_3029_){
_start:
{
lean_object* v_fst_3030_; lean_object* v_fst_3031_; uint8_t v___x_3032_; 
v_fst_3030_ = lean_ctor_get(v_x1_3028_, 0);
v_fst_3031_ = lean_ctor_get(v_x2_3029_, 0);
v___x_3032_ = l_Lean_Name_quickLt(v_fst_3030_, v_fst_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3033_, lean_object* v_x2_3034_){
_start:
{
uint8_t v_res_3035_; lean_object* v_r_3036_; 
v_res_3035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3033_, v_x2_3034_);
lean_dec_ref(v_x2_3034_);
lean_dec_ref(v_x1_3033_);
v_r_3036_ = lean_box(v_res_3035_);
return v_r_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3037_, lean_object* v_pivot_3038_, lean_object* v_as_3039_, lean_object* v_i_3040_, lean_object* v_k_3041_){
_start:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_nat_dec_lt(v_k_3041_, v_hi_3037_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec(v_k_3041_);
v___x_3043_ = lean_array_fswap(v_as_3039_, v_i_3040_, v_hi_3037_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v_i_3040_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; lean_object* v_fst_3046_; lean_object* v_fst_3047_; uint8_t v___x_3048_; 
v___x_3045_ = lean_array_fget_borrowed(v_as_3039_, v_k_3041_);
v_fst_3046_ = lean_ctor_get(v___x_3045_, 0);
v_fst_3047_ = lean_ctor_get(v_pivot_3038_, 0);
v___x_3048_ = l_Lean_Name_quickLt(v_fst_3046_, v_fst_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_unsigned_to_nat(1u);
v___x_3050_ = lean_nat_add(v_k_3041_, v___x_3049_);
lean_dec(v_k_3041_);
v_k_3041_ = v___x_3050_;
goto _start;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3052_ = lean_array_fswap(v_as_3039_, v_i_3040_, v_k_3041_);
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_nat_add(v_i_3040_, v___x_3053_);
lean_dec(v_i_3040_);
v___x_3055_ = lean_nat_add(v_k_3041_, v___x_3053_);
lean_dec(v_k_3041_);
v_as_3039_ = v___x_3052_;
v_i_3040_ = v___x_3054_;
v_k_3041_ = v___x_3055_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3057_, lean_object* v_pivot_3058_, lean_object* v_as_3059_, lean_object* v_i_3060_, lean_object* v_k_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3057_, v_pivot_3058_, v_as_3059_, v_i_3060_, v_k_3061_);
lean_dec_ref(v_pivot_3058_);
lean_dec(v_hi_3057_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3063_, lean_object* v_as_3064_, lean_object* v_lo_3065_, lean_object* v_hi_3066_){
_start:
{
lean_object* v___y_3068_; uint8_t v___x_3078_; 
v___x_3078_ = lean_nat_dec_lt(v_lo_3065_, v_hi_3066_);
if (v___x_3078_ == 0)
{
lean_dec(v_lo_3065_);
return v_as_3064_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_mid_3081_; lean_object* v___y_3083_; lean_object* v___y_3089_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3079_ = lean_nat_add(v_lo_3065_, v_hi_3066_);
v___x_3080_ = lean_unsigned_to_nat(1u);
v_mid_3081_ = lean_nat_shiftr(v___x_3079_, v___x_3080_);
lean_dec(v___x_3079_);
v___x_3094_ = lean_array_fget_borrowed(v_as_3064_, v_mid_3081_);
v___x_3095_ = lean_array_fget_borrowed(v_as_3064_, v_lo_3065_);
v___x_3096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
v___y_3089_ = v_as_3064_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_array_fswap(v_as_3064_, v_lo_3065_, v_mid_3081_);
v___y_3089_ = v___x_3097_;
goto v___jp_3088_;
}
v___jp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3084_ = lean_array_fget_borrowed(v___y_3083_, v_mid_3081_);
v___x_3085_ = lean_array_fget_borrowed(v___y_3083_, v_hi_3066_);
v___x_3086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec(v_mid_3081_);
v___y_3068_ = v___y_3083_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_array_fswap(v___y_3083_, v_mid_3081_, v_hi_3066_);
lean_dec(v_mid_3081_);
v___y_3068_ = v___x_3087_;
goto v___jp_3067_;
}
}
v___jp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = lean_array_fget_borrowed(v___y_3089_, v_hi_3066_);
v___x_3091_ = lean_array_fget_borrowed(v___y_3089_, v_lo_3065_);
v___x_3092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
v___y_3083_ = v___y_3089_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_array_fswap(v___y_3089_, v_lo_3065_, v_hi_3066_);
v___y_3083_ = v___x_3093_;
goto v___jp_3082_;
}
}
}
v___jp_3067_:
{
lean_object* v_pivot_3069_; lean_object* v___x_3070_; lean_object* v_fst_3071_; lean_object* v_snd_3072_; uint8_t v___x_3073_; 
v_pivot_3069_ = lean_array_fget(v___y_3068_, v_hi_3066_);
lean_inc_n(v_lo_3065_, 2);
v___x_3070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3066_, v_pivot_3069_, v___y_3068_, v_lo_3065_, v_lo_3065_);
lean_dec(v_pivot_3069_);
v_fst_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_fst_3071_);
v_snd_3072_ = lean_ctor_get(v___x_3070_, 1);
lean_inc(v_snd_3072_);
lean_dec_ref(v___x_3070_);
v___x_3073_ = lean_nat_dec_le(v_hi_3066_, v_fst_3071_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3063_, v_snd_3072_, v_lo_3065_, v_fst_3071_);
v___x_3075_ = lean_unsigned_to_nat(1u);
v___x_3076_ = lean_nat_add(v_fst_3071_, v___x_3075_);
lean_dec(v_fst_3071_);
v_as_3064_ = v___x_3074_;
v_lo_3065_ = v___x_3076_;
goto _start;
}
else
{
lean_dec(v_fst_3071_);
lean_dec(v_lo_3065_);
return v_snd_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3098_, lean_object* v_as_3099_, lean_object* v_lo_3100_, lean_object* v_hi_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3098_, v_as_3099_, v_lo_3100_, v_hi_3101_);
lean_dec(v_hi_3101_);
lean_dec(v_n_3098_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3105_, lean_object* v_s_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___x_3116_; 
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3109_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3108_, v_s_3106_);
v___x_3110_ = lean_array_get_size(v___x_3109_);
v___x_3116_ = lean_nat_dec_eq(v___x_3110_, v___x_3107_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___y_3120_; uint8_t v___x_3122_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_sub(v___x_3110_, v___x_3117_);
v___x_3122_ = lean_nat_dec_le(v___x_3107_, v___x_3118_);
if (v___x_3122_ == 0)
{
lean_inc(v___x_3118_);
v___y_3120_ = v___x_3118_;
goto v___jp_3119_;
}
else
{
v___y_3120_ = v___x_3107_;
goto v___jp_3119_;
}
v___jp_3119_:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_nat_dec_le(v___y_3120_, v___x_3118_);
if (v___x_3121_ == 0)
{
lean_dec(v___x_3118_);
lean_inc(v___y_3120_);
v___y_3112_ = v___y_3120_;
v___y_3113_ = v___y_3120_;
goto v___jp_3111_;
}
else
{
v___y_3112_ = v___y_3120_;
v___y_3113_ = v___x_3118_;
goto v___jp_3111_;
}
}
}
else
{
lean_object* v___x_3123_; 
lean_inc_ref_n(v___x_3109_, 2);
v___x_3123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3109_);
lean_ctor_set(v___x_3123_, 1, v___x_3109_);
lean_ctor_set(v___x_3123_, 2, v___x_3109_);
return v___x_3123_;
}
v___jp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3110_, v___x_3109_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_inc_ref_n(v___x_3114_, 2);
v___x_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
lean_ctor_set(v___x_3115_, 2, v___x_3114_);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3124_, lean_object* v_s_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3124_, v_s_3125_);
lean_dec(v_s_3125_);
lean_dec_ref(v_x_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3129_, v_es_3127_);
v___x_3131_ = lean_array_get_size(v___x_3130_);
v___x_3132_ = lean_nat_dec_eq(v___x_3131_, v___x_3128_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___y_3136_; uint8_t v___x_3140_; 
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = lean_nat_sub(v___x_3131_, v___x_3133_);
v___x_3140_ = lean_nat_dec_le(v___x_3128_, v___x_3134_);
if (v___x_3140_ == 0)
{
lean_inc(v___x_3134_);
v___y_3136_ = v___x_3134_;
goto v___jp_3135_;
}
else
{
v___y_3136_ = v___x_3128_;
goto v___jp_3135_;
}
v___jp_3135_:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_nat_dec_le(v___y_3136_, v___x_3134_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec(v___x_3134_);
lean_inc(v___y_3136_);
v___x_3138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3131_, v___x_3130_, v___y_3136_, v___y_3136_);
lean_dec(v___y_3136_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3131_, v___x_3130_, v___y_3136_, v___x_3134_);
lean_dec(v___x_3134_);
return v___x_3139_;
}
}
}
else
{
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3141_);
lean_dec(v_es_3141_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3143_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3148_, lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3148_, v_x_3149_, v___y_3150_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v_x_3149_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3180_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3183_, lean_object* v_t_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3183_, v_t_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3186_, lean_object* v_t_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3186_, v_t_3187_);
lean_dec(v_t_3187_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3189_, lean_object* v_as_3190_, lean_object* v_lo_3191_, lean_object* v_hi_3192_, lean_object* v_w_3193_, lean_object* v_hlo_3194_, lean_object* v_hhi_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3189_, v_as_3190_, v_lo_3191_, v_hi_3192_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3197_, lean_object* v_as_3198_, lean_object* v_lo_3199_, lean_object* v_hi_3200_, lean_object* v_w_3201_, lean_object* v_hlo_3202_, lean_object* v_hhi_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3197_, v_as_3198_, v_lo_3199_, v_hi_3200_, v_w_3201_, v_hlo_3202_, v_hhi_3203_);
lean_dec(v_hi_3200_);
lean_dec(v_n_3197_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3205_, lean_object* v_lo_3206_, lean_object* v_hi_3207_, lean_object* v_hhi_3208_, lean_object* v_pivot_3209_, lean_object* v_as_3210_, lean_object* v_i_3211_, lean_object* v_k_3212_, lean_object* v_ilo_3213_, lean_object* v_ik_3214_, lean_object* v_w_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3207_, v_pivot_3209_, v_as_3210_, v_i_3211_, v_k_3212_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3217_, lean_object* v_lo_3218_, lean_object* v_hi_3219_, lean_object* v_hhi_3220_, lean_object* v_pivot_3221_, lean_object* v_as_3222_, lean_object* v_i_3223_, lean_object* v_k_3224_, lean_object* v_ilo_3225_, lean_object* v_ik_3226_, lean_object* v_w_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(v_n_3217_, v_lo_3218_, v_hi_3219_, v_hhi_3220_, v_pivot_3221_, v_as_3222_, v_i_3223_, v_k_3224_, v_ilo_3225_, v_ik_3226_, v_w_3227_);
lean_dec_ref(v_pivot_3221_);
lean_dec(v_hi_3219_);
lean_dec(v_lo_3218_);
lean_dec(v_n_3217_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3229_, lean_object* v_k_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_m_3235_; lean_object* v_a_3236_; uint8_t v___x_3237_; 
v___x_3233_ = lean_nat_add(v_x_3231_, v_x_3232_);
v___x_3234_ = lean_unsigned_to_nat(1u);
v_m_3235_ = lean_nat_shiftr(v___x_3233_, v___x_3234_);
lean_dec(v___x_3233_);
v_a_3236_ = lean_array_fget_borrowed(v_as_3229_, v_m_3235_);
v___x_3237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3236_, v_k_3230_);
if (v___x_3237_ == 0)
{
uint8_t v___x_3238_; 
lean_dec(v_x_3232_);
v___x_3238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3230_, v_a_3236_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_dec(v_m_3235_);
lean_dec(v_x_3231_);
lean_inc(v_a_3236_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_a_3236_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = lean_unsigned_to_nat(0u);
v___x_3241_ = lean_nat_dec_eq(v_m_3235_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = lean_nat_sub(v_m_3235_, v___x_3234_);
lean_dec(v_m_3235_);
v___x_3243_ = lean_nat_dec_lt(v___x_3242_, v_x_3231_);
if (v___x_3243_ == 0)
{
v_x_3232_ = v___x_3242_;
goto _start;
}
else
{
lean_object* v___x_3245_; 
lean_dec(v___x_3242_);
lean_dec(v_x_3231_);
v___x_3245_ = lean_box(0);
return v___x_3245_;
}
}
else
{
lean_object* v___x_3246_; 
lean_dec(v_m_3235_);
lean_dec(v_x_3231_);
v___x_3246_ = lean_box(0);
return v___x_3246_;
}
}
}
else
{
lean_object* v___x_3247_; uint8_t v___x_3248_; 
lean_dec(v_x_3231_);
v___x_3247_ = lean_nat_add(v_m_3235_, v___x_3234_);
lean_dec(v_m_3235_);
v___x_3248_ = lean_nat_dec_le(v___x_3247_, v_x_3232_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec(v___x_3247_);
lean_dec(v_x_3232_);
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
else
{
v_x_3231_ = v___x_3247_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3251_, lean_object* v_k_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3251_, v_k_3252_, v_x_3253_, v_x_3254_);
lean_dec_ref(v_k_3252_);
lean_dec_ref(v_as_3251_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3256_, lean_object* v_as_3257_, size_t v_sz_3258_, size_t v_i_3259_, lean_object* v_b_3260_){
_start:
{
lean_object* v_a_3262_; uint8_t v___x_3266_; 
v___x_3266_ = lean_usize_dec_lt(v_i_3259_, v_sz_3258_);
if (v___x_3266_ == 0)
{
lean_dec(v_tactic_3256_);
return v_b_3260_;
}
else
{
lean_object* v___x_3267_; lean_object* v_a_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3267_ = lean_unsigned_to_nat(0u);
v_a_3268_ = lean_array_uget_borrowed(v_as_3257_, v_i_3259_);
v___x_3269_ = lean_array_get_size(v_a_3268_);
v___x_3270_ = lean_nat_dec_lt(v___x_3267_, v___x_3269_);
if (v___x_3270_ == 0)
{
v_a_3262_ = v_b_3260_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3271_ = lean_unsigned_to_nat(1u);
v___x_3272_ = lean_nat_sub(v___x_3269_, v___x_3271_);
v___x_3273_ = lean_nat_dec_le(v___x_3267_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_dec(v___x_3272_);
v_a_3262_ = v_b_3260_;
goto v___jp_3261_;
}
else
{
lean_object* v_extensions_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_extensions_3274_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3256_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v_tactic_3256_);
lean_ctor_set(v___x_3275_, 1, v_extensions_3274_);
v___x_3276_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3268_, v___x_3275_, v___x_3267_, v___x_3272_);
lean_dec_ref_known(v___x_3275_, 2);
if (lean_obj_tag(v___x_3276_) == 1)
{
lean_object* v_val_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; 
v_val_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v_snd_3278_ = lean_ctor_get(v_val_3277_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_val_3277_);
v___x_3279_ = l_Array_append___redArg(v_b_3260_, v_snd_3278_);
lean_dec(v_snd_3278_);
v_a_3262_ = v___x_3279_;
goto v___jp_3261_;
}
else
{
lean_dec(v___x_3276_);
v_a_3262_ = v_b_3260_;
goto v___jp_3261_;
}
}
}
}
v___jp_3261_:
{
size_t v___x_3263_; size_t v___x_3264_; 
v___x_3263_ = ((size_t)1ULL);
v___x_3264_ = lean_usize_add(v_i_3259_, v___x_3263_);
v_i_3259_ = v___x_3264_;
v_b_3260_ = v_a_3262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3280_, lean_object* v_as_3281_, lean_object* v_sz_3282_, lean_object* v_i_3283_, lean_object* v_b_3284_){
_start:
{
size_t v_sz_boxed_3285_; size_t v_i_boxed_3286_; lean_object* v_res_3287_; 
v_sz_boxed_3285_ = lean_unbox_usize(v_sz_3282_);
lean_dec(v_sz_3282_);
v_i_boxed_3286_ = lean_unbox_usize(v_i_3283_);
lean_dec(v_i_3283_);
v_res_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3280_, v_as_3281_, v_sz_boxed_3285_, v_i_boxed_3286_, v_b_3284_);
lean_dec_ref(v_as_3281_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3288_, lean_object* v_tactic_3289_){
_start:
{
lean_object* v___x_3290_; lean_object* v_toEnvExtension_3291_; lean_object* v_asyncMode_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v_importedEntries_3298_; lean_object* v_extensions_3299_; size_t v_sz_3300_; size_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3290_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3291_ = lean_ctor_get(v___x_3290_, 0);
v_asyncMode_3292_ = lean_ctor_get(v_toEnvExtension_3291_, 2);
v___x_3293_ = lean_box(1);
v___x_3294_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
v___x_3295_ = lean_box(0);
v___x_3296_ = 0;
lean_inc_ref(v_env_3288_);
v___x_3297_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3294_, v_toEnvExtension_3291_, v_env_3288_, v_asyncMode_3292_, v___x_3295_, v___x_3296_);
v_importedEntries_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc_ref(v_importedEntries_3298_);
lean_dec(v___x_3297_);
v_extensions_3299_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3300_ = lean_array_size(v_importedEntries_3298_);
v___x_3301_ = ((size_t)0ULL);
lean_inc(v_tactic_3289_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3289_, v_importedEntries_3298_, v_sz_3300_, v___x_3301_, v_extensions_3299_);
lean_dec_ref(v_importedEntries_3298_);
v___x_3303_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3293_, v___x_3290_, v_env_3288_, v_asyncMode_3292_, v___x_3295_, v___x_3296_);
v___x_3304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3303_, v_tactic_3289_);
lean_dec(v_tactic_3289_);
lean_dec(v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 1)
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l_Array_append___redArg(v___x_3302_, v_val_3305_);
lean_dec(v_val_3305_);
return v___x_3306_;
}
else
{
lean_dec(v___x_3304_);
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3307_, lean_object* v_k_3308_, lean_object* v_x_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3307_, v_k_3308_, v_x_3309_, v_x_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3313_, lean_object* v_k_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3313_, v_k_3314_, v_x_3315_, v_x_3316_, v_x_3317_);
lean_dec_ref(v_k_3314_);
lean_dec_ref(v_as_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3319_, lean_object* v_pos_3320_){
_start:
{
lean_object* v_str_3321_; lean_object* v_startInclusive_3322_; lean_object* v_endExclusive_3323_; lean_object* v___x_3324_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v_decide_3335_; 
v_str_3321_ = lean_ctor_get(v_s_3319_, 0);
v_startInclusive_3322_ = lean_ctor_get(v_s_3319_, 1);
v_endExclusive_3323_ = lean_ctor_get(v_s_3319_, 2);
v___x_3324_ = lean_nat_add(v_startInclusive_3322_, v_pos_3320_);
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_nat_sub(v_endExclusive_3323_, v___x_3324_);
v_decide_3335_ = lean_nat_dec_eq(v___x_3333_, v___x_3334_);
lean_dec(v___x_3334_);
if (v_decide_3335_ == 0)
{
uint32_t v___x_3336_; uint32_t v___x_3337_; uint8_t v___x_3338_; 
v___x_3336_ = lean_string_utf8_get_fast(v_str_3321_, v___x_3324_);
v___x_3337_ = 32;
v___x_3338_ = lean_uint32_dec_eq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
uint32_t v___x_3339_; uint8_t v___x_3340_; 
v___x_3339_ = 9;
v___x_3340_ = lean_uint32_dec_eq(v___x_3336_, v___x_3339_);
if (v___x_3340_ == 0)
{
uint32_t v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = 13;
v___x_3342_ = lean_uint32_dec_eq(v___x_3336_, v___x_3341_);
if (v___x_3342_ == 0)
{
uint32_t v___x_3343_; uint8_t v___x_3344_; 
v___x_3343_ = 10;
v___x_3344_ = lean_uint32_dec_eq(v___x_3336_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec(v___x_3324_);
return v_pos_3320_;
}
else
{
goto v___jp_3325_;
}
}
else
{
goto v___jp_3325_;
}
}
else
{
goto v___jp_3325_;
}
}
else
{
goto v___jp_3325_;
}
}
else
{
lean_dec(v___x_3324_);
return v_pos_3320_;
}
v___jp_3325_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3326_ = lean_string_utf8_next_fast(v_str_3321_, v___x_3324_);
v___x_3327_ = lean_nat_sub(v___x_3326_, v___x_3324_);
lean_dec(v___x_3324_);
v___x_3328_ = lean_nat_add(v_pos_3320_, v___x_3327_);
lean_dec(v___x_3327_);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_nat_add(v_pos_3320_, v___x_3329_);
v___x_3331_ = lean_nat_dec_le(v___x_3330_, v___x_3328_);
lean_dec(v___x_3330_);
if (v___x_3331_ == 0)
{
lean_dec(v___x_3328_);
return v_pos_3320_;
}
else
{
lean_dec(v_pos_3320_);
v_pos_3320_ = v___x_3328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3345_, lean_object* v_pos_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3345_, v_pos_3346_);
lean_dec_ref(v_s_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3350_){
_start:
{
lean_object* v___y_3352_; lean_object* v_str_3355_; lean_object* v_startInclusive_3356_; lean_object* v_endExclusive_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v_decide_3361_; 
v_str_3355_ = lean_ctor_get(v_str_3350_, 0);
v_startInclusive_3356_ = lean_ctor_get(v_str_3350_, 1);
v_endExclusive_3357_ = lean_ctor_get(v_str_3350_, 2);
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3350_, v___x_3358_);
v___x_3360_ = lean_nat_sub(v_endExclusive_3357_, v_startInclusive_3356_);
v_decide_3361_ = lean_nat_dec_eq(v___x_3359_, v___x_3360_);
lean_dec(v___x_3360_);
lean_dec(v___x_3359_);
if (v_decide_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3363_ = lean_string_utf8_extract_fast(v_str_3355_, v_startInclusive_3356_, v_endExclusive_3357_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___y_3352_ = v___x_3364_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_string_utf8_extract_fast(v_str_3355_, v_startInclusive_3356_, v_endExclusive_3357_);
v___y_3352_ = v___x_3365_;
goto v___jp_3351_;
}
v___jp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3354_ = lean_string_append(v___y_3352_, v___x_3353_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3366_);
lean_dec_ref(v_str_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg(){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___closed__0));
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg___boxed(lean_object* v___dummy_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg();
return v_res_3373_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___redArg();
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3375_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3377_);
lean_dec_ref(v_s_3377_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3379_, lean_object* v___x_3380_, lean_object* v___x_3381_, lean_object* v_a_3382_, lean_object* v_b_3383_){
_start:
{
lean_object* v_it_3385_; lean_object* v_startInclusive_3386_; lean_object* v_endExclusive_3387_; 
if (lean_obj_tag(v_a_3382_) == 0)
{
lean_object* v_currPos_3391_; lean_object* v_searcher_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3415_; 
v_currPos_3391_ = lean_ctor_get(v_a_3382_, 0);
v_searcher_3392_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3394_ = v_a_3382_;
v_isShared_3395_ = v_isSharedCheck_3415_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_searcher_3392_);
lean_inc(v_currPos_3391_);
lean_dec(v_a_3382_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3415_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
uint8_t v_decide_3396_; 
v_decide_3396_ = lean_nat_dec_eq(v_searcher_3392_, v___x_3381_);
if (v_decide_3396_ == 0)
{
uint32_t v___x_3397_; uint32_t v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = 10;
v___x_3398_ = lean_string_utf8_get_fast(v_str_3379_, v_searcher_3392_);
v___x_3399_ = lean_uint32_dec_eq(v___x_3398_, v___x_3397_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_string_utf8_next_fast(v_str_3379_, v_searcher_3392_);
lean_dec(v_searcher_3392_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 1, v___x_3400_);
v___x_3402_ = v___x_3394_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_currPos_3391_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
v_a_3382_ = v___x_3402_;
goto _start;
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_slice_3408_; lean_object* v_nextIt_3410_; 
v___x_3405_ = lean_string_utf8_next_fast(v_str_3379_, v_searcher_3392_);
v___x_3406_ = lean_nat_sub(v___x_3405_, v_searcher_3392_);
v___x_3407_ = lean_nat_add(v_searcher_3392_, v___x_3406_);
lean_dec(v___x_3406_);
v_slice_3408_ = l_String_Slice_subslice_x21(v___x_3380_, v_currPos_3391_, v_searcher_3392_);
lean_inc(v___x_3407_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 1, v___x_3407_);
lean_ctor_set(v___x_3394_, 0, v___x_3407_);
v_nextIt_3410_ = v___x_3394_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3407_);
v_nextIt_3410_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v_startInclusive_3411_; lean_object* v_endExclusive_3412_; 
v_startInclusive_3411_ = lean_ctor_get(v_slice_3408_, 0);
lean_inc(v_startInclusive_3411_);
v_endExclusive_3412_ = lean_ctor_get(v_slice_3408_, 1);
lean_inc(v_endExclusive_3412_);
lean_dec_ref(v_slice_3408_);
v_it_3385_ = v_nextIt_3410_;
v_startInclusive_3386_ = v_startInclusive_3411_;
v_endExclusive_3387_ = v_endExclusive_3412_;
goto v___jp_3384_;
}
}
}
else
{
lean_object* v___x_3414_; 
lean_del_object(v___x_3394_);
lean_dec(v_searcher_3392_);
v___x_3414_ = lean_box(1);
lean_inc(v___x_3381_);
v_it_3385_ = v___x_3414_;
v_startInclusive_3386_ = v_currPos_3391_;
v_endExclusive_3387_ = v___x_3381_;
goto v___jp_3384_;
}
}
}
else
{
lean_dec(v___x_3381_);
lean_dec_ref(v_str_3379_);
return v_b_3383_;
}
v___jp_3384_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_inc_ref(v_str_3379_);
v___x_3388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3388_, 0, v_str_3379_);
lean_ctor_set(v___x_3388_, 1, v_startInclusive_3386_);
lean_ctor_set(v___x_3388_, 2, v_endExclusive_3387_);
v___x_3389_ = lean_array_push(v_b_3383_, v___x_3388_);
v_a_3382_ = v_it_3385_;
v_b_3383_ = v___x_3389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3416_, lean_object* v___x_3417_, lean_object* v___x_3418_, lean_object* v_a_3419_, lean_object* v_b_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3416_, v___x_3417_, v___x_3418_, v_a_3419_, v_b_3420_);
lean_dec_ref(v___x_3417_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
return v_x_3422_;
}
else
{
lean_object* v_head_3424_; lean_object* v_tail_3425_; lean_object* v___x_3426_; 
v_head_3424_ = lean_ctor_get(v_x_3423_, 0);
v_tail_3425_ = lean_ctor_get(v_x_3423_, 1);
v___x_3426_ = lean_string_append(v_x_3422_, v_head_3424_);
v_x_3422_ = v___x_3426_;
v_x_3423_ = v_tail_3425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3428_, lean_object* v_x_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3428_, v_x_3429_);
lean_dec(v_x_3429_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
if (lean_obj_tag(v_a_3431_) == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = l_List_reverse___redArg(v_a_3432_);
return v___x_3433_;
}
else
{
lean_object* v_head_3434_; lean_object* v_tail_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3444_; 
v_head_3434_ = lean_ctor_get(v_a_3431_, 0);
v_tail_3435_ = lean_ctor_get(v_a_3431_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3431_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3437_ = v_a_3431_;
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_tail_3435_);
lean_inc(v_head_3434_);
lean_dec(v_a_3431_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3434_);
lean_dec(v_head_3434_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v_a_3432_);
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_a_3432_);
v___x_3441_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v_a_3431_ = v_tail_3435_;
v_a_3432_ = v___x_3441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v_lines_3456_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = lean_string_utf8_byte_size(v_str_3449_);
lean_inc_ref(v_str_3449_);
v___x_3452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3452_, 0, v_str_3449_);
lean_ctor_set(v___x_3452_, 1, v___x_3450_);
lean_ctor_set(v___x_3452_, 2, v___x_3451_);
v___x_3453_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0);
v___x_3454_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3455_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3449_, v___x_3452_, v___x_3451_, v___x_3453_, v___x_3454_);
lean_dec_ref_known(v___x_3452_, 3);
v_lines_3456_ = lean_array_to_list(v___x_3455_);
if (lean_obj_tag(v_lines_3456_) == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
return v___x_3457_;
}
else
{
lean_object* v_tail_3458_; 
v_tail_3458_ = lean_ctor_get(v_lines_3456_, 1);
if (lean_obj_tag(v_tail_3458_) == 0)
{
lean_object* v_head_3459_; lean_object* v_str_3460_; lean_object* v_startInclusive_3461_; lean_object* v_endExclusive_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_head_3459_ = lean_ctor_get(v_lines_3456_, 0);
lean_inc(v_head_3459_);
lean_dec_ref_known(v_lines_3456_, 2);
v_str_3460_ = lean_ctor_get(v_head_3459_, 0);
lean_inc_ref(v_str_3460_);
v_startInclusive_3461_ = lean_ctor_get(v_head_3459_, 1);
lean_inc(v_startInclusive_3461_);
v_endExclusive_3462_ = lean_ctor_get(v_head_3459_, 2);
lean_inc(v_endExclusive_3462_);
lean_dec(v_head_3459_);
v___x_3463_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3464_ = lean_string_utf8_extract_fast(v_str_3460_, v_startInclusive_3461_, v_endExclusive_3462_);
lean_dec(v_endExclusive_3462_);
lean_dec(v_startInclusive_3461_);
lean_dec_ref(v_str_3460_);
v___x_3465_ = lean_string_append(v___x_3463_, v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
return v___x_3467_;
}
else
{
lean_object* v_head_3468_; lean_object* v_str_3469_; lean_object* v_startInclusive_3470_; lean_object* v_endExclusive_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_inc(v_tail_3458_);
v_head_3468_ = lean_ctor_get(v_lines_3456_, 0);
lean_inc(v_head_3468_);
lean_dec_ref_known(v_lines_3456_, 2);
v_str_3469_ = lean_ctor_get(v_head_3468_, 0);
lean_inc_ref(v_str_3469_);
v_startInclusive_3470_ = lean_ctor_get(v_head_3468_, 1);
lean_inc(v_startInclusive_3470_);
v_endExclusive_3471_ = lean_ctor_get(v_head_3468_, 2);
lean_inc(v_endExclusive_3471_);
lean_dec(v_head_3468_);
v___x_3472_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3473_ = lean_string_utf8_extract_fast(v_str_3469_, v_startInclusive_3470_, v_endExclusive_3471_);
lean_dec(v_endExclusive_3471_);
lean_dec(v_startInclusive_3470_);
lean_dec_ref(v_str_3469_);
v___x_3474_ = lean_string_append(v___x_3472_, v___x_3473_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3476_ = lean_string_append(v___x_3474_, v___x_3475_);
v___x_3477_ = lean_box(0);
v___x_3478_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3458_, v___x_3477_);
v___x_3479_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3480_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3479_, v___x_3478_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_string_append(v___x_3476_, v___x_3480_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3483_ = lean_string_append(v___x_3481_, v___x_3482_);
return v___x_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3484_, lean_object* v___x_3485_, lean_object* v___x_3486_, lean_object* v_inst_3487_, lean_object* v_R_3488_, lean_object* v_a_3489_, lean_object* v_b_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3484_, v___x_3485_, v___x_3486_, v_a_3489_, v_b_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3492_, lean_object* v___x_3493_, lean_object* v___x_3494_, lean_object* v_inst_3495_, lean_object* v_R_3496_, lean_object* v_a_3497_, lean_object* v_b_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3492_, v___x_3493_, v___x_3494_, v_inst_3495_, v_R_3496_, v_a_3497_, v_b_3498_);
lean_dec_ref(v___x_3493_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
if (lean_obj_tag(v_a_3500_) == 0)
{
lean_object* v___x_3502_; 
v___x_3502_ = l_List_reverse___redArg(v_a_3501_);
return v___x_3502_;
}
else
{
lean_object* v_head_3503_; lean_object* v_tail_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3513_; 
v_head_3503_ = lean_ctor_get(v_a_3500_, 0);
v_tail_3504_ = lean_ctor_get(v_a_3500_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_a_3500_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3506_ = v_a_3500_;
v_isShared_3507_ = v_isSharedCheck_3513_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_tail_3504_);
lean_inc(v_head_3503_);
lean_dec(v_a_3500_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3513_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3503_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_a_3501_);
lean_ctor_set(v___x_3506_, 0, v___x_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3501_);
v___x_3510_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
v_a_3500_ = v_tail_3504_;
v_a_3501_ = v___x_3510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3514_, lean_object* v_pos_3515_){
_start:
{
lean_object* v_str_3516_; lean_object* v_startInclusive_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v_decide_3521_; 
v_str_3516_ = lean_ctor_get(v_s_3514_, 0);
v_startInclusive_3517_ = lean_ctor_get(v_s_3514_, 1);
v___x_3518_ = lean_nat_add(v_startInclusive_3517_, v_pos_3515_);
v___x_3519_ = lean_nat_sub(v___x_3518_, v_startInclusive_3517_);
v___x_3520_ = lean_unsigned_to_nat(0u);
v_decide_3521_ = lean_nat_dec_eq(v___x_3519_, v___x_3520_);
if (v_decide_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3530_; uint32_t v___x_3531_; uint32_t v___x_3532_; uint8_t v___x_3533_; 
lean_inc(v_startInclusive_3517_);
lean_inc_ref(v_str_3516_);
v___x_3522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3522_, 0, v_str_3516_);
lean_ctor_set(v___x_3522_, 1, v_startInclusive_3517_);
lean_ctor_set(v___x_3522_, 2, v___x_3518_);
v___x_3523_ = lean_unsigned_to_nat(1u);
v___x_3524_ = lean_nat_sub(v___x_3519_, v___x_3523_);
lean_dec(v___x_3519_);
v___x_3525_ = l_String_Slice_posLE(v___x_3522_, v___x_3524_);
lean_dec_ref_known(v___x_3522_, 3);
v___x_3530_ = lean_nat_add(v_startInclusive_3517_, v___x_3525_);
v___x_3531_ = lean_string_utf8_get_fast(v_str_3516_, v___x_3530_);
lean_dec(v___x_3530_);
v___x_3532_ = 32;
v___x_3533_ = lean_uint32_dec_eq(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
uint32_t v___x_3534_; uint8_t v___x_3535_; 
v___x_3534_ = 9;
v___x_3535_ = lean_uint32_dec_eq(v___x_3531_, v___x_3534_);
if (v___x_3535_ == 0)
{
uint32_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3536_ = 13;
v___x_3537_ = lean_uint32_dec_eq(v___x_3531_, v___x_3536_);
if (v___x_3537_ == 0)
{
uint32_t v___x_3538_; uint8_t v___x_3539_; 
v___x_3538_ = 10;
v___x_3539_ = lean_uint32_dec_eq(v___x_3531_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec(v___x_3525_);
return v_pos_3515_;
}
else
{
goto v___jp_3526_;
}
}
else
{
goto v___jp_3526_;
}
}
else
{
goto v___jp_3526_;
}
}
else
{
goto v___jp_3526_;
}
v___jp_3526_:
{
lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3527_ = lean_nat_add(v___x_3525_, v___x_3523_);
v___x_3528_ = lean_nat_dec_le(v___x_3527_, v_pos_3515_);
lean_dec(v___x_3527_);
if (v___x_3528_ == 0)
{
lean_dec(v___x_3525_);
return v_pos_3515_;
}
else
{
lean_dec(v_pos_3515_);
v_pos_3515_ = v___x_3525_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3519_);
lean_dec(v___x_3518_);
return v_pos_3515_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3540_, lean_object* v_pos_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3540_, v_pos_3541_);
lean_dec_ref(v_s_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3544_, lean_object* v_tactic_3545_){
_start:
{
lean_object* v_exts_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_exts_3546_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3544_, v_tactic_3545_);
v___x_3547_ = lean_array_get_size(v_exts_3546_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = lean_nat_dec_eq(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3550_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3551_ = lean_array_to_list(v_exts_3546_);
v___x_3552_ = lean_box(0);
v___x_3553_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3551_, v___x_3552_);
v___x_3554_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3555_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3554_, v___x_3553_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_string_append(v___x_3550_, v___x_3555_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = lean_string_utf8_byte_size(v___x_3556_);
lean_inc_ref(v___x_3556_);
v___x_3558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3548_);
lean_ctor_set(v___x_3558_, 2, v___x_3557_);
v___x_3559_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3558_, v___x_3557_);
lean_dec_ref_known(v___x_3558_, 3);
v___x_3560_ = lean_string_utf8_extract_fast(v___x_3556_, v___x_3548_, v___x_3559_);
lean_dec(v___x_3559_);
lean_dec_ref(v___x_3556_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; 
lean_dec_ref(v_exts_3546_);
v___x_3561_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3562_, lean_object* v_x_3563_){
_start:
{
lean_object* v_fst_3564_; lean_object* v_snd_3565_; lean_object* v___x_3566_; 
v_fst_3564_ = lean_ctor_get(v_x_3563_, 0);
lean_inc(v_fst_3564_);
v_snd_3565_ = lean_ctor_get(v_x_3563_, 1);
lean_inc(v_snd_3565_);
lean_dec_ref(v_x_3563_);
v___x_3566_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3564_, v_snd_3565_, v_as_3562_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3567_, lean_object* v_x_3568_){
_start:
{
if (lean_obj_tag(v_x_3568_) == 0)
{
lean_object* v_k_3569_; lean_object* v_v_3570_; lean_object* v_l_3571_; lean_object* v_r_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_k_3569_ = lean_ctor_get(v_x_3568_, 1);
v_v_3570_ = lean_ctor_get(v_x_3568_, 2);
v_l_3571_ = lean_ctor_get(v_x_3568_, 3);
v_r_3572_ = lean_ctor_get(v_x_3568_, 4);
v___x_3573_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3567_, v_l_3571_);
lean_inc(v_v_3570_);
lean_inc(v_k_3569_);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v_k_3569_);
lean_ctor_set(v___x_3574_, 1, v_v_3570_);
v___x_3575_ = lean_array_push(v___x_3573_, v___x_3574_);
v_init_3567_ = v___x_3575_;
v_x_3568_ = v_r_3572_;
goto _start;
}
else
{
return v_init_3567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3577_, v_x_3578_);
lean_dec(v_x_3578_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3580_, lean_object* v_pivot_3581_, lean_object* v_as_3582_, lean_object* v_i_3583_, lean_object* v_k_3584_){
_start:
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_nat_dec_lt(v_k_3584_, v_hi_3580_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec(v_k_3584_);
v___x_3586_ = lean_array_fswap(v_as_3582_, v_i_3583_, v_hi_3580_);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v_i_3583_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
return v___x_3587_;
}
else
{
lean_object* v___x_3588_; lean_object* v_fst_3589_; lean_object* v_fst_3590_; uint8_t v___x_3591_; 
v___x_3588_ = lean_array_fget_borrowed(v_as_3582_, v_k_3584_);
v_fst_3589_ = lean_ctor_get(v___x_3588_, 0);
v_fst_3590_ = lean_ctor_get(v_pivot_3581_, 0);
v___x_3591_ = l_Lean_Name_quickLt(v_fst_3589_, v_fst_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_unsigned_to_nat(1u);
v___x_3593_ = lean_nat_add(v_k_3584_, v___x_3592_);
lean_dec(v_k_3584_);
v_k_3584_ = v___x_3593_;
goto _start;
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3595_ = lean_array_fswap(v_as_3582_, v_i_3583_, v_k_3584_);
v___x_3596_ = lean_unsigned_to_nat(1u);
v___x_3597_ = lean_nat_add(v_i_3583_, v___x_3596_);
lean_dec(v_i_3583_);
v___x_3598_ = lean_nat_add(v_k_3584_, v___x_3596_);
lean_dec(v_k_3584_);
v_as_3582_ = v___x_3595_;
v_i_3583_ = v___x_3597_;
v_k_3584_ = v___x_3598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3600_, lean_object* v_pivot_3601_, lean_object* v_as_3602_, lean_object* v_i_3603_, lean_object* v_k_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3600_, v_pivot_3601_, v_as_3602_, v_i_3603_, v_k_3604_);
lean_dec_ref(v_pivot_3601_);
lean_dec(v_hi_3600_);
return v_res_3605_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3606_, lean_object* v_x2_3607_){
_start:
{
lean_object* v_fst_3608_; lean_object* v_fst_3609_; uint8_t v___x_3610_; 
v_fst_3608_ = lean_ctor_get(v_x1_3606_, 0);
v_fst_3609_ = lean_ctor_get(v_x2_3607_, 0);
v___x_3610_ = l_Lean_Name_quickLt(v_fst_3608_, v_fst_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3611_, lean_object* v_x2_3612_){
_start:
{
uint8_t v_res_3613_; lean_object* v_r_3614_; 
v_res_3613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3611_, v_x2_3612_);
lean_dec_ref(v_x2_3612_);
lean_dec_ref(v_x1_3611_);
v_r_3614_ = lean_box(v_res_3613_);
return v_r_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3615_, lean_object* v_as_3616_, lean_object* v_lo_3617_, lean_object* v_hi_3618_){
_start:
{
lean_object* v___y_3620_; uint8_t v___x_3630_; 
v___x_3630_ = lean_nat_dec_lt(v_lo_3617_, v_hi_3618_);
if (v___x_3630_ == 0)
{
lean_dec(v_lo_3617_);
return v_as_3616_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v_mid_3633_; lean_object* v___y_3635_; lean_object* v___y_3641_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3631_ = lean_nat_add(v_lo_3617_, v_hi_3618_);
v___x_3632_ = lean_unsigned_to_nat(1u);
v_mid_3633_ = lean_nat_shiftr(v___x_3631_, v___x_3632_);
lean_dec(v___x_3631_);
v___x_3646_ = lean_array_fget_borrowed(v_as_3616_, v_mid_3633_);
v___x_3647_ = lean_array_fget_borrowed(v_as_3616_, v_lo_3617_);
v___x_3648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3646_, v___x_3647_);
if (v___x_3648_ == 0)
{
v___y_3641_ = v_as_3616_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_array_fswap(v_as_3616_, v_lo_3617_, v_mid_3633_);
v___y_3641_ = v___x_3649_;
goto v___jp_3640_;
}
v___jp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3636_ = lean_array_fget_borrowed(v___y_3635_, v_mid_3633_);
v___x_3637_ = lean_array_fget_borrowed(v___y_3635_, v_hi_3618_);
v___x_3638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3636_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec(v_mid_3633_);
v___y_3620_ = v___y_3635_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_array_fswap(v___y_3635_, v_mid_3633_, v_hi_3618_);
lean_dec(v_mid_3633_);
v___y_3620_ = v___x_3639_;
goto v___jp_3619_;
}
}
v___jp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3642_ = lean_array_fget_borrowed(v___y_3641_, v_hi_3618_);
v___x_3643_ = lean_array_fget_borrowed(v___y_3641_, v_lo_3617_);
v___x_3644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
v___y_3635_ = v___y_3641_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_array_fswap(v___y_3641_, v_lo_3617_, v_hi_3618_);
v___y_3635_ = v___x_3645_;
goto v___jp_3634_;
}
}
}
v___jp_3619_:
{
lean_object* v_pivot_3621_; lean_object* v___x_3622_; lean_object* v_fst_3623_; lean_object* v_snd_3624_; uint8_t v___x_3625_; 
v_pivot_3621_ = lean_array_fget(v___y_3620_, v_hi_3618_);
lean_inc_n(v_lo_3617_, 2);
v___x_3622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3618_, v_pivot_3621_, v___y_3620_, v_lo_3617_, v_lo_3617_);
lean_dec(v_pivot_3621_);
v_fst_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_fst_3623_);
v_snd_3624_ = lean_ctor_get(v___x_3622_, 1);
lean_inc(v_snd_3624_);
lean_dec_ref(v___x_3622_);
v___x_3625_ = lean_nat_dec_le(v_hi_3618_, v_fst_3623_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3615_, v_snd_3624_, v_lo_3617_, v_fst_3623_);
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3628_ = lean_nat_add(v_fst_3623_, v___x_3627_);
lean_dec(v_fst_3623_);
v_as_3616_ = v___x_3626_;
v_lo_3617_ = v___x_3628_;
goto _start;
}
else
{
lean_dec(v_fst_3623_);
lean_dec(v_lo_3617_);
return v_snd_3624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3650_, lean_object* v_as_3651_, lean_object* v_lo_3652_, lean_object* v_hi_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3650_, v_as_3651_, v_lo_3652_, v_hi_3653_);
lean_dec(v_hi_3653_);
lean_dec(v_n_3650_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3657_, lean_object* v_s_3658_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___y_3664_; lean_object* v___y_3665_; uint8_t v___x_3668_; 
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3661_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3660_, v_s_3658_);
v___x_3662_ = lean_array_get_size(v___x_3661_);
v___x_3668_ = lean_nat_dec_eq(v___x_3662_, v___x_3659_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___y_3672_; uint8_t v___x_3674_; 
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_nat_sub(v___x_3662_, v___x_3669_);
v___x_3674_ = lean_nat_dec_le(v___x_3659_, v___x_3670_);
if (v___x_3674_ == 0)
{
lean_inc(v___x_3670_);
v___y_3672_ = v___x_3670_;
goto v___jp_3671_;
}
else
{
v___y_3672_ = v___x_3659_;
goto v___jp_3671_;
}
v___jp_3671_:
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_nat_dec_le(v___y_3672_, v___x_3670_);
if (v___x_3673_ == 0)
{
lean_dec(v___x_3670_);
lean_inc(v___y_3672_);
v___y_3664_ = v___y_3672_;
v___y_3665_ = v___y_3672_;
goto v___jp_3663_;
}
else
{
v___y_3664_ = v___y_3672_;
v___y_3665_ = v___x_3670_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v___x_3675_; 
lean_inc_ref_n(v___x_3661_, 2);
v___x_3675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3661_);
lean_ctor_set(v___x_3675_, 1, v___x_3661_);
lean_ctor_set(v___x_3675_, 2, v___x_3661_);
return v___x_3675_;
}
v___jp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3662_, v___x_3661_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_inc_ref_n(v___x_3666_, 2);
v___x_3667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
lean_ctor_set(v___x_3667_, 2, v___x_3666_);
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3676_, lean_object* v_s_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3676_, v_s_3677_);
lean_dec(v_s_3677_);
lean_dec_ref(v_x_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3679_){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3680_ = lean_unsigned_to_nat(0u);
v___x_3681_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3682_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3681_, v_es_3679_);
v___x_3683_ = lean_array_get_size(v___x_3682_);
v___x_3684_ = lean_nat_dec_eq(v___x_3683_, v___x_3680_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___y_3688_; uint8_t v___x_3692_; 
v___x_3685_ = lean_unsigned_to_nat(1u);
v___x_3686_ = lean_nat_sub(v___x_3683_, v___x_3685_);
v___x_3692_ = lean_nat_dec_le(v___x_3680_, v___x_3686_);
if (v___x_3692_ == 0)
{
lean_inc(v___x_3686_);
v___y_3688_ = v___x_3686_;
goto v___jp_3687_;
}
else
{
v___y_3688_ = v___x_3680_;
goto v___jp_3687_;
}
v___jp_3687_:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_nat_dec_le(v___y_3688_, v___x_3686_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
lean_dec(v___x_3686_);
lean_inc(v___y_3688_);
v___x_3690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3683_, v___x_3682_, v___y_3688_, v___y_3688_);
lean_dec(v___y_3688_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; 
v___x_3691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3683_, v___x_3682_, v___y_3688_, v___x_3686_);
lean_dec(v___x_3686_);
return v___x_3691_;
}
}
}
else
{
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_3693_);
lean_dec(v_es_3693_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_3695_, lean_object* v_x_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3695_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_3700_, v_x_3701_, v___y_3702_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_x_3701_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3732_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_3735_, lean_object* v_t_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3735_, v_t_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3738_, lean_object* v_t_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_3738_, v_t_3739_);
lean_dec(v_t_3739_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_3741_, lean_object* v_as_3742_, lean_object* v_lo_3743_, lean_object* v_hi_3744_, lean_object* v_w_3745_, lean_object* v_hlo_3746_, lean_object* v_hhi_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3741_, v_as_3742_, v_lo_3743_, v_hi_3744_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3749_, lean_object* v_as_3750_, lean_object* v_lo_3751_, lean_object* v_hi_3752_, lean_object* v_w_3753_, lean_object* v_hlo_3754_, lean_object* v_hhi_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_3749_, v_as_3750_, v_lo_3751_, v_hi_3752_, v_w_3753_, v_hlo_3754_, v_hhi_3755_);
lean_dec(v_hi_3752_);
lean_dec(v_n_3749_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3757_, lean_object* v_lo_3758_, lean_object* v_hi_3759_, lean_object* v_hhi_3760_, lean_object* v_pivot_3761_, lean_object* v_as_3762_, lean_object* v_i_3763_, lean_object* v_k_3764_, lean_object* v_ilo_3765_, lean_object* v_ik_3766_, lean_object* v_w_3767_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3759_, v_pivot_3761_, v_as_3762_, v_i_3763_, v_k_3764_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3769_, lean_object* v_lo_3770_, lean_object* v_hi_3771_, lean_object* v_hhi_3772_, lean_object* v_pivot_3773_, lean_object* v_as_3774_, lean_object* v_i_3775_, lean_object* v_k_3776_, lean_object* v_ilo_3777_, lean_object* v_ik_3778_, lean_object* v_w_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(v_n_3769_, v_lo_3770_, v_hi_3771_, v_hhi_3772_, v_pivot_3773_, v_as_3774_, v_i_3775_, v_k_3776_, v_ilo_3777_, v_ik_3778_, v_w_3779_);
lean_dec_ref(v_pivot_3773_);
lean_dec(v_hi_3771_);
lean_dec(v_lo_3770_);
lean_dec(v_n_3769_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_3782_, lean_object* v___x_3783_, lean_object* v_toPure_3784_, lean_object* v___f_3785_, lean_object* v_env_3786_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3786_, v_tac_3782_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3791_; lean_object* v_toEnvExtension_3792_; lean_object* v_asyncMode_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec_ref(v___f_3785_);
v___x_3791_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3792_ = lean_ctor_get(v___x_3791_, 0);
v_asyncMode_3793_ = lean_ctor_get(v_toEnvExtension_3792_, 2);
v___x_3794_ = lean_box(0);
v___x_3795_ = 0;
v___x_3796_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3783_, v___x_3791_, v_env_3786_, v_asyncMode_3793_, v___x_3794_, v___x_3795_);
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3796_, v_tac_3782_);
lean_dec(v_tac_3782_);
lean_dec(v___x_3796_);
v___x_3798_ = lean_apply_2(v_toPure_3784_, lean_box(0), v___x_3797_);
return v___x_3798_;
}
else
{
lean_object* v_val_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v_val_3799_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3800_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3801_ = 0;
v___x_3802_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3783_, v___x_3800_, v_env_3786_, v_val_3799_, v___x_3801_);
lean_dec(v_val_3799_);
lean_dec_ref(v_env_3786_);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_array_get_size(v___x_3802_);
v___x_3805_ = lean_nat_dec_lt(v___x_3803_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_dec_ref(v___x_3802_);
lean_dec_ref(v___f_3785_);
lean_dec(v_tac_3782_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_sub(v___x_3804_, v___x_3806_);
v___x_3808_ = lean_nat_dec_le(v___x_3803_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_dec(v___x_3807_);
lean_dec_ref(v___x_3802_);
lean_dec_ref(v___f_3785_);
lean_dec(v_tac_3782_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3809_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v_tac_3782_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_3812_ = l_Array_binSearchAux___redArg(v___f_3785_, v___x_3811_, v___x_3802_, v___x_3810_, v___x_3803_, v___x_3807_);
lean_dec_ref(v___x_3802_);
if (lean_obj_tag(v___x_3812_) == 0)
{
goto v___jp_3787_;
}
else
{
lean_object* v_val_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3822_; 
v_val_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_val_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v_snd_3817_; lean_object* v___x_3819_; 
v_snd_3817_ = lean_ctor_get(v_val_3813_, 1);
lean_inc(v_snd_3817_);
lean_dec(v_val_3813_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v_snd_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_snd_3817_);
v___x_3819_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_apply_2(v_toPure_3784_, lean_box(0), v___x_3819_);
return v___x_3820_;
}
}
}
}
}
}
v___jp_3787_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_apply_2(v_toPure_3784_, lean_box(0), v___x_3788_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_3824_, lean_object* v_inst_3825_, lean_object* v_tac_3826_){
_start:
{
lean_object* v_toApplicative_3827_; lean_object* v_toBind_3828_; lean_object* v_getEnv_3829_; lean_object* v_toPure_3830_; lean_object* v___f_3831_; lean_object* v___x_3832_; lean_object* v___f_3833_; lean_object* v___x_3834_; 
v_toApplicative_3827_ = lean_ctor_get(v_inst_3824_, 0);
lean_inc_ref(v_toApplicative_3827_);
v_toBind_3828_ = lean_ctor_get(v_inst_3824_, 1);
lean_inc(v_toBind_3828_);
lean_dec_ref(v_inst_3824_);
v_getEnv_3829_ = lean_ctor_get(v_inst_3825_, 0);
lean_inc(v_getEnv_3829_);
lean_dec_ref(v_inst_3825_);
v_toPure_3830_ = lean_ctor_get(v_toApplicative_3827_, 1);
lean_inc(v_toPure_3830_);
lean_dec_ref(v_toApplicative_3827_);
v___f_3831_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0));
v___x_3832_ = lean_box(1);
v___f_3833_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3833_, 0, v_tac_3826_);
lean_closure_set(v___f_3833_, 1, v___x_3832_);
lean_closure_set(v___f_3833_, 2, v_toPure_3830_);
lean_closure_set(v___f_3833_, 3, v___f_3831_);
v___x_3834_ = lean_apply_4(v_toBind_3828_, lean_box(0), lean_box(0), v_getEnv_3829_, v___f_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_3835_, lean_object* v_inst_3836_, lean_object* v_inst_3837_, lean_object* v_tac_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_3836_, v_inst_3837_, v_tac_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v_addEntryFn_3840_, lean_object* v___x_3841_, lean_object* v_s_3842_){
_start:
{
lean_object* v_importedEntries_3843_; lean_object* v_state_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3852_; 
v_importedEntries_3843_ = lean_ctor_get(v_s_3842_, 0);
v_state_3844_ = lean_ctor_get(v_s_3842_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_s_3842_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3846_ = v_s_3842_;
v_isShared_3847_ = v_isSharedCheck_3852_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_state_3844_);
lean_inc(v_importedEntries_3843_);
lean_dec(v_s_3842_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3852_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_state_3848_; lean_object* v___x_3850_; 
v_state_3848_ = lean_apply_2(v_addEntryFn_3840_, v_state_3844_, v___x_3841_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v_state_3848_);
v___x_3850_ = v___x_3846_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_importedEntries_3843_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_state_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_3853_, lean_object* v_k_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_m_3859_; lean_object* v_a_3860_; uint8_t v___x_3861_; 
v___x_3857_ = lean_nat_add(v_x_3855_, v_x_3856_);
v___x_3858_ = lean_unsigned_to_nat(1u);
v_m_3859_ = lean_nat_shiftr(v___x_3857_, v___x_3858_);
lean_dec(v___x_3857_);
v_a_3860_ = lean_array_fget_borrowed(v_as_3853_, v_m_3859_);
v___x_3861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3860_, v_k_3854_);
if (v___x_3861_ == 0)
{
uint8_t v___x_3862_; 
lean_dec(v_x_3856_);
v___x_3862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3854_, v_a_3860_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec(v_m_3859_);
lean_dec(v_x_3855_);
lean_inc(v_a_3860_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_a_3860_);
return v___x_3863_;
}
else
{
lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_nat_dec_eq(v_m_3859_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3866_ = lean_nat_sub(v_m_3859_, v___x_3858_);
lean_dec(v_m_3859_);
v___x_3867_ = lean_nat_dec_lt(v___x_3866_, v_x_3855_);
if (v___x_3867_ == 0)
{
v_x_3856_ = v___x_3866_;
goto _start;
}
else
{
lean_object* v___x_3869_; 
lean_dec(v___x_3866_);
lean_dec(v_x_3855_);
v___x_3869_ = lean_box(0);
return v___x_3869_;
}
}
else
{
lean_object* v___x_3870_; 
lean_dec(v_m_3859_);
lean_dec(v_x_3855_);
v___x_3870_ = lean_box(0);
return v___x_3870_;
}
}
}
else
{
lean_object* v___x_3871_; uint8_t v___x_3872_; 
lean_dec(v_x_3855_);
v___x_3871_ = lean_nat_add(v_m_3859_, v___x_3858_);
lean_dec(v_m_3859_);
v___x_3872_ = lean_nat_dec_le(v___x_3871_, v_x_3856_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; 
lean_dec(v___x_3871_);
lean_dec(v_x_3856_);
v___x_3873_ = lean_box(0);
return v___x_3873_;
}
else
{
v_x_3855_ = v___x_3871_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_3875_, lean_object* v_k_3876_, lean_object* v_x_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3875_, v_k_3876_, v_x_3877_, v_x_3878_);
lean_dec_ref(v_k_3876_);
lean_dec_ref(v_as_3875_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_env_3888_; lean_object* v___x_3889_; 
v___x_3883_ = lean_box(1);
v___x_3884_ = lean_st_ref_get(v___y_3881_);
v_env_3888_ = lean_ctor_get(v___x_3884_, 0);
lean_inc_ref(v_env_3888_);
lean_dec(v___x_3884_);
v___x_3889_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3888_, v_tac_3880_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3890_; lean_object* v_toEnvExtension_3891_; lean_object* v_asyncMode_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3890_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3891_ = lean_ctor_get(v___x_3890_, 0);
v_asyncMode_3892_ = lean_ctor_get(v_toEnvExtension_3891_, 2);
v___x_3893_ = lean_box(0);
v___x_3894_ = 0;
v___x_3895_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3883_, v___x_3890_, v_env_3888_, v_asyncMode_3892_, v___x_3893_, v___x_3894_);
v___x_3896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3895_, v_tac_3880_);
lean_dec(v_tac_3880_);
lean_dec(v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
else
{
lean_object* v_val_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3926_; 
v_val_3898_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3900_ = v___x_3889_;
v_isShared_3901_ = v_isSharedCheck_3926_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_val_3898_);
lean_dec(v___x_3889_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3926_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3902_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3903_ = 0;
v___x_3904_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3883_, v___x_3902_, v_env_3888_, v_val_3898_, v___x_3903_);
lean_dec(v_val_3898_);
lean_dec_ref(v_env_3888_);
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_array_get_size(v___x_3904_);
v___x_3907_ = lean_nat_dec_lt(v___x_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_dec_ref(v___x_3904_);
lean_del_object(v___x_3900_);
lean_dec(v_tac_3880_);
goto v___jp_3885_;
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_sub(v___x_3906_, v___x_3908_);
v___x_3910_ = lean_nat_dec_le(v___x_3905_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_dec(v___x_3909_);
lean_dec_ref(v___x_3904_);
lean_del_object(v___x_3900_);
lean_dec(v_tac_3880_);
goto v___jp_3885_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4_spec__6___closed__1));
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_tac_3880_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_3904_, v___x_3912_, v___x_3905_, v___x_3909_);
lean_dec_ref_known(v___x_3912_, 2);
lean_dec_ref(v___x_3904_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_del_object(v___x_3900_);
goto v___jp_3885_;
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3925_; 
v_val_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3925_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_val_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3925_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v_snd_3918_; lean_object* v___x_3920_; 
v_snd_3918_ = lean_ctor_get(v_val_3914_, 1);
lean_inc(v_snd_3918_);
lean_dec(v_val_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v_snd_3918_);
v___x_3920_ = v___x_3916_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_snd_3918_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3920_);
v___x_3922_ = v___x_3900_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
}
}
v___jp_3885_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_3927_, v___y_3928_);
lean_dec(v___y_3928_);
return v_res_3930_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3933_ = l_Lean_stringToMessageData(v___x_3932_);
return v___x_3933_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
return v___x_3936_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3939_ = l_Lean_stringToMessageData(v___x_3938_);
return v___x_3939_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3942_ = l_Lean_stringToMessageData(v___x_3941_);
return v___x_3942_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3945_ = l_Lean_stringToMessageData(v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_3952_, lean_object* v___x_3953_, lean_object* v___x_3954_, lean_object* v___x_3955_, lean_object* v_name_3956_, lean_object* v_decl_3957_, lean_object* v_stx_3958_, uint8_t v_kind_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v_nextMacroScope_3966_; lean_object* v_ngen_3967_; lean_object* v_auxDeclNGen_3968_; lean_object* v_traceState_3969_; lean_object* v_recordedDeps_3970_; lean_object* v_messages_3971_; lean_object* v_infoState_3972_; lean_object* v_snapshotTasks_3973_; lean_object* v___y_3974_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; uint8_t v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v_name_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; uint8_t v___x_4129_; uint8_t v___x_4130_; 
v___x_4129_ = 0;
v___x_4130_ = l_Lean_instBEqAttributeKind_beq(v_kind_3959_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; 
lean_dec(v_stx_3958_);
lean_dec(v_decl_3957_);
lean_dec_ref(v___x_3955_);
lean_dec_ref(v___x_3954_);
lean_dec_ref(v___x_3953_);
lean_dec(v___x_3952_);
v___x_4131_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__6___redArg(v_name_3956_, v_kind_3959_, v___y_3960_, v___y_3961_);
return v___x_4131_;
}
else
{
goto v___jp_4088_;
}
v___jp_3963_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3975_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__3_spec__4___closed__1);
v___x_3976_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3976_, 0, v___y_3974_);
lean_ctor_set(v___x_3976_, 1, v_nextMacroScope_3966_);
lean_ctor_set(v___x_3976_, 2, v_ngen_3967_);
lean_ctor_set(v___x_3976_, 3, v_auxDeclNGen_3968_);
lean_ctor_set(v___x_3976_, 4, v_traceState_3969_);
lean_ctor_set(v___x_3976_, 5, v___x_3975_);
lean_ctor_set(v___x_3976_, 6, v_recordedDeps_3970_);
lean_ctor_set(v___x_3976_, 7, v_messages_3971_);
lean_ctor_set(v___x_3976_, 8, v_infoState_3972_);
lean_ctor_set(v___x_3976_, 9, v_snapshotTasks_3973_);
v___x_3977_ = lean_st_ref_put(v___y_3965_, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___y_3964_);
return v___x_3978_;
}
v___jp_3979_:
{
lean_object* v___x_3982_; lean_object* v_env_3983_; lean_object* v_nextMacroScope_3984_; lean_object* v_ngen_3985_; lean_object* v_auxDeclNGen_3986_; lean_object* v_traceState_3987_; lean_object* v_recordedDeps_3988_; lean_object* v_messages_3989_; lean_object* v_infoState_3990_; lean_object* v_snapshotTasks_3991_; lean_object* v___x_3992_; lean_object* v_toEnvExtension_3993_; lean_object* v_addEntryFn_3994_; lean_object* v_asyncMode_3995_; uint8_t v_logWrites_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___f_3999_; uint8_t v___x_4000_; 
v___x_3982_ = lean_st_ref_take(v___y_3981_);
v_env_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc_ref(v_env_3983_);
v_nextMacroScope_3984_ = lean_ctor_get(v___x_3982_, 1);
lean_inc(v_nextMacroScope_3984_);
v_ngen_3985_ = lean_ctor_get(v___x_3982_, 2);
lean_inc_ref(v_ngen_3985_);
v_auxDeclNGen_3986_ = lean_ctor_get(v___x_3982_, 3);
lean_inc_ref(v_auxDeclNGen_3986_);
v_traceState_3987_ = lean_ctor_get(v___x_3982_, 4);
lean_inc_ref(v_traceState_3987_);
v_recordedDeps_3988_ = lean_ctor_get(v___x_3982_, 6);
lean_inc_ref(v_recordedDeps_3988_);
v_messages_3989_ = lean_ctor_get(v___x_3982_, 7);
lean_inc_ref(v_messages_3989_);
v_infoState_3990_ = lean_ctor_get(v___x_3982_, 8);
lean_inc_ref(v_infoState_3990_);
v_snapshotTasks_3991_ = lean_ctor_get(v___x_3982_, 9);
lean_inc_ref(v_snapshotTasks_3991_);
lean_dec(v___x_3982_);
v___x_3992_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3993_ = lean_ctor_get(v___x_3992_, 0);
v_addEntryFn_3994_ = lean_ctor_get(v___x_3992_, 3);
v_asyncMode_3995_ = lean_ctor_get(v_toEnvExtension_3993_, 2);
v_logWrites_3996_ = lean_ctor_get_uint8(v_toEnvExtension_3993_, sizeof(void*)*6);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v_decl_3957_);
lean_ctor_set(v___x_3998_, 1, v___y_3980_);
lean_inc(v_addEntryFn_3994_);
v___f_3999_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_3999_, 0, v_addEntryFn_3994_);
lean_closure_set(v___f_3999_, 1, v___x_3998_);
v___x_4000_ = 1;
if (v_logWrites_3996_ == 0)
{
lean_object* v___x_4001_; 
lean_inc_ref(v_toEnvExtension_3993_);
v___x_4001_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3993_, v_env_3983_, v___f_3999_, v_asyncMode_3995_, v___x_3952_, v___x_4000_);
v___y_3964_ = v___x_3997_;
v___y_3965_ = v___y_3981_;
v_nextMacroScope_3966_ = v_nextMacroScope_3984_;
v_ngen_3967_ = v_ngen_3985_;
v_auxDeclNGen_3968_ = v_auxDeclNGen_3986_;
v_traceState_3969_ = v_traceState_3987_;
v_recordedDeps_3970_ = v_recordedDeps_3988_;
v_messages_3971_ = v_messages_3989_;
v_infoState_3972_ = v_infoState_3990_;
v_snapshotTasks_3973_ = v_snapshotTasks_3991_;
v___y_3974_ = v___x_4001_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_inc_ref_n(v_toEnvExtension_3993_, 2);
v___x_4002_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3993_, v_env_3983_);
lean_dec_ref(v_env_3983_);
v___x_4003_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3993_, v___x_4002_, v___f_3999_, v_asyncMode_3995_, v___x_3952_, v___x_4000_);
v___y_3964_ = v___x_3997_;
v___y_3965_ = v___y_3981_;
v_nextMacroScope_3966_ = v_nextMacroScope_3984_;
v_ngen_3967_ = v_ngen_3985_;
v_auxDeclNGen_3968_ = v_auxDeclNGen_3986_;
v_traceState_3969_ = v_traceState_3987_;
v_recordedDeps_3970_ = v_recordedDeps_3988_;
v_messages_3971_ = v_messages_3989_;
v_infoState_3972_ = v_infoState_3990_;
v_snapshotTasks_3973_ = v_snapshotTasks_3991_;
v___y_3974_ = v___x_4003_;
goto v___jp_3963_;
}
}
v___jp_4004_:
{
lean_object* v___x_4008_; lean_object* v_a_4009_; 
lean_inc(v_decl_3957_);
v___x_4008_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_3957_, v___y_4007_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
if (lean_obj_tag(v_a_4009_) == 1)
{
lean_object* v_val_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec_ref(v___y_4005_);
lean_dec(v___x_3952_);
v_val_4010_ = lean_ctor_get(v_a_4009_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v_a_4009_, 1);
v___x_4011_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4012_ = 0;
v___x_4013_ = l_Lean_MessageData_ofConstName(v_decl_3957_, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4011_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = l_Lean_stringToMessageData(v_val_4010_);
v___x_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4016_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4018_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4020_, v___y_4006_, v___y_4007_);
return v___x_4021_;
}
else
{
lean_dec(v_a_4009_);
v___y_3980_ = v___y_4005_;
v___y_3981_ = v___y_4007_;
goto v___jp_3979_;
}
}
v___jp_4022_:
{
lean_object* v___x_4026_; lean_object* v_env_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_st_ref_get(v___y_4025_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
lean_inc(v_decl_3957_);
v___x_4028_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4027_, v_decl_3957_);
if (lean_obj_tag(v___x_4028_) == 1)
{
lean_object* v_val_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v___y_4023_);
lean_dec(v___x_3952_);
v_val_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_val_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4031_ = 0;
v___x_4032_ = l_Lean_MessageData_ofConstName(v_decl_3957_, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4030_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4033_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = l_Lean_MessageData_ofConstName(v_val_4029_, v___x_4031_);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v___x_4030_);
v___x_4039_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3958_, v___x_4038_, v___y_4024_, v___y_4025_);
lean_dec(v_stx_3958_);
return v___x_4039_;
}
else
{
lean_dec(v___x_4028_);
lean_dec(v_stx_3958_);
v___y_4005_ = v___y_4023_;
v___y_4006_ = v___y_4024_;
v___y_4007_ = v___y_4025_;
goto v___jp_4004_;
}
}
v___jp_4040_:
{
lean_object* v___x_4045_; lean_object* v_env_4046_; lean_object* v___x_4047_; 
v___x_4045_ = lean_st_ref_get(v___y_4044_);
v_env_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc_ref(v_env_4046_);
lean_dec(v___x_4045_);
v___x_4047_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4046_, v_decl_3957_);
lean_dec_ref(v_env_4046_);
if (lean_obj_tag(v___x_4047_) == 1)
{
lean_object* v_val_4048_; lean_object* v___x_4049_; lean_object* v_env_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
lean_dec_ref(v___y_4042_);
lean_dec(v___x_3952_);
v_val_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v___x_4047_, 1);
v___x_4049_ = lean_st_ref_get(v___y_4044_);
v_env_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc_ref(v_env_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = l_Lean_Environment_allImportedModuleNames(v_env_4050_);
lean_dec_ref(v_env_4050_);
v___x_4052_ = lean_array_get_size(v___x_4051_);
v___x_4053_ = lean_nat_dec_lt(v_val_4048_, v___x_4052_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec_ref(v___x_4051_);
lean_dec(v_val_4048_);
v___x_4054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4055_ = l_Lean_MessageData_ofConstName(v_decl_3957_, v___y_4041_);
v___x_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4054_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3958_, v___x_4058_, v___y_4043_, v___y_4044_);
lean_dec(v_stx_3958_);
return v___x_4059_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4060_ = lean_array_fget(v___x_4051_, v_val_4048_);
lean_dec(v_val_4048_);
lean_dec_ref(v___x_4051_);
v___x_4061_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4062_ = l_Lean_MessageData_ofConstName(v_decl_3957_, v___y_4041_);
v___x_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4063_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
v___x_4066_ = l_Lean_MessageData_ofName(v___x_4060_);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3958_, v___x_4069_, v___y_4043_, v___y_4044_);
lean_dec(v_stx_3958_);
return v___x_4070_;
}
}
else
{
lean_dec(v___x_4047_);
v___y_4023_ = v___y_4042_;
v___y_4024_ = v___y_4043_;
v___y_4025_ = v___y_4044_;
goto v___jp_4022_;
}
}
v___jp_4071_:
{
lean_object* v___x_4075_; lean_object* v_env_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; 
v___x_4075_ = lean_st_ref_get(v___y_4074_);
v_env_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_ref(v_env_4076_);
lean_dec(v___x_4075_);
v___x_4077_ = 0;
lean_inc(v_decl_3957_);
v___x_4078_ = l_Lean_Environment_find_x3f(v_env_4076_, v_decl_3957_, v___x_4077_);
if (lean_obj_tag(v___x_4078_) == 0)
{
v___y_4023_ = v_name_4072_;
v___y_4024_ = v___y_4073_;
v___y_4025_ = v___y_4074_;
goto v___jp_4022_;
}
else
{
lean_object* v___x_4079_; lean_object* v_env_4080_; uint8_t v___x_4081_; 
lean_dec_ref_known(v___x_4078_, 1);
v___x_4079_ = lean_st_ref_get(v___y_4074_);
v_env_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc_ref(v_env_4080_);
lean_dec(v___x_4079_);
v___x_4081_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4080_, v_decl_3957_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec_ref(v_name_4072_);
lean_dec(v___x_3952_);
v___x_4082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4083_ = l_Lean_MessageData_ofConstName(v_decl_3957_, v___x_4077_);
v___x_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4082_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4084_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__4___redArg(v_stx_3958_, v___x_4086_, v___y_4073_, v___y_4074_);
lean_dec(v_stx_3958_);
return v___x_4087_;
}
else
{
v___y_4041_ = v___x_4077_;
v___y_4042_ = v_name_4072_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___y_4074_;
goto v___jp_4040_;
}
}
}
v___jp_4088_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4090_ = l_Lean_Name_mkStr4(v___x_3953_, v___x_3954_, v___x_4089_, v___x_3955_);
lean_inc(v_stx_3958_);
v___x_4091_ = l_Lean_Syntax_isOfKind(v_stx_3958_, v___x_4090_);
lean_dec(v___x_4090_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_stx_3958_);
lean_dec(v_decl_3957_);
lean_dec(v___x_3952_);
v___x_4092_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4093_ = l_Lean_MessageData_ofName(v_name_3956_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4096_, v___y_3960_, v___y_3961_);
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
else
{
lean_object* v___x_4106_; lean_object* v_name_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4106_ = lean_unsigned_to_nat(1u);
v_name_4107_ = l_Lean_Syntax_getArg(v_stx_3958_, v___x_4106_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4107_);
v___x_4109_ = l_Lean_Syntax_isOfKind(v_name_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4110_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4107_);
v___x_4111_ = l_Lean_Syntax_isOfKind(v_name_4107_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_name_4107_);
lean_dec(v_stx_3958_);
lean_dec(v_decl_3957_);
lean_dec(v___x_3952_);
v___x_4112_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4113_ = l_Lean_MessageData_ofName(v_name_3956_);
v___x_4114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4112_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4114_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4116_, v___y_3960_, v___y_3961_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec(v_name_3956_);
v___x_4126_ = l_Lean_TSyntax_getId(v_name_4107_);
lean_dec(v_name_4107_);
v___x_4127_ = l_Lean_Name_toString(v___x_4126_, v___x_4109_);
v_name_4072_ = v___x_4127_;
v___y_4073_ = v___y_3960_;
v___y_4074_ = v___y_3961_;
goto v___jp_4071_;
}
}
else
{
lean_object* v___x_4128_; 
lean_dec(v_name_3956_);
v___x_4128_ = l_Lean_TSyntax_getString(v_name_4107_);
lean_dec(v_name_4107_);
v_name_4072_ = v___x_4128_;
v___y_4073_ = v___y_3960_;
v___y_4074_ = v___y_3961_;
goto v___jp_4071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v___x_4132_, lean_object* v___x_4133_, lean_object* v___x_4134_, lean_object* v___x_4135_, lean_object* v_name_4136_, lean_object* v_decl_4137_, lean_object* v_stx_4138_, lean_object* v_kind_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
uint8_t v_kind_boxed_4143_; lean_object* v_res_4144_; 
v_kind_boxed_4143_ = lean_unbox(v_kind_4139_);
v_res_4144_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(v___x_4132_, v___x_4133_, v___x_4134_, v___x_4135_, v_name_4136_, v_decl_4137_, v_stx_4138_, v_kind_boxed_4143_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4144_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = lean_unsigned_to_nat(3374007381u);
v___x_4157_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4158_ = l_Lean_Name_num___override(v___x_4157_, v___x_4156_);
return v___x_4158_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4160_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4161_ = l_Lean_Name_str___override(v___x_4160_, v___x_4159_);
return v___x_4161_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4162_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_));
v___x_4163_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4164_ = l_Lean_Name_str___override(v___x_4163_, v___x_4162_);
return v___x_4164_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4165_ = lean_unsigned_to_nat(2u);
v___x_4166_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4167_ = l_Lean_Name_num___override(v___x_4166_, v___x_4165_);
return v___x_4167_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v_name_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4169_ = 2;
v___x_4170_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v_name_4171_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4172_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4173_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v_name_4171_);
lean_ctor_set(v___x_4173_, 2, v___x_4170_);
lean_ctor_set_uint8(v___x_4173_, sizeof(void*)*3, v___x_4169_);
return v___x_4173_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4174_; lean_object* v___f_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___f_4174_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___f_4175_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4176_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___f_4175_);
lean_ctor_set(v___x_4177_, 2, v___f_4174_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4180_ = l_Lean_registerBuiltinAttribute(v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object* v_tac_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4183_, v___y_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tac_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(v_tac_4188_, v___y_4189_, v___y_4190_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4193_, lean_object* v_k_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4193_, v_k_4194_, v_x_4195_, v_x_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4199_, lean_object* v_k_4200_, lean_object* v_x_4201_, lean_object* v_x_4202_, lean_object* v_x_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(v_as_4199_, v_k_4200_, v_x_4201_, v_x_4202_, v_x_4203_);
lean_dec_ref(v_k_4200_);
lean_dec_ref(v_as_4199_);
return v_res_4204_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0));
v___x_4207_ = l_Lean_stringToMessageData(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object* v___x_4208_, lean_object* v___x_4209_, lean_object* v_catName_4210_, lean_object* v_declName_4211_, uint8_t v___builtIn_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; uint8_t v___x_4217_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4242_; lean_object* v___y_4243_; 
v___x_4216_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_4217_ = lean_name_eq(v_catName_4210_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4259_; lean_object* v_env_4260_; lean_object* v___x_4261_; 
v___x_4259_ = lean_st_ref_get(v___y_4214_);
v_env_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc_ref(v_env_4260_);
lean_dec(v___x_4259_);
lean_inc(v_declName_4211_);
v___x_4261_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4260_, v_declName_4211_);
if (lean_obj_tag(v___x_4261_) == 0)
{
v___y_4242_ = v___y_4213_;
v___y_4243_ = v___y_4214_;
goto v___jp_4241_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec_ref_known(v___x_4261_, 1);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
v___x_4262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4263_ = l_Lean_MessageData_ofConstName(v_declName_4211_, v___x_4217_);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4266_, v___y_4213_, v___y_4214_);
return v___x_4267_;
}
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec(v_declName_4211_);
lean_dec(v___x_4209_);
lean_dec(v___x_4208_);
v___x_4268_ = lean_box(0);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
v___jp_4218_:
{
lean_object* v___x_4221_; lean_object* v_env_4222_; lean_object* v___x_4223_; lean_object* v_toEnvExtension_4224_; lean_object* v_asyncMode_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4221_ = lean_st_ref_get(v___y_4220_);
v_env_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc_ref(v_env_4222_);
lean_dec(v___x_4221_);
v___x_4223_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4224_ = lean_ctor_get(v___x_4223_, 0);
v_asyncMode_4225_ = lean_ctor_get(v_toEnvExtension_4224_, 2);
v___x_4226_ = lean_box(0);
v___x_4227_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4208_, v___x_4223_, v_env_4222_, v_asyncMode_4225_, v___x_4226_, v___x_4217_);
v___x_4228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4227_, v_declName_4211_);
lean_dec(v___x_4227_);
if (lean_obj_tag(v___x_4228_) == 1)
{
lean_object* v_val_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_val_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_val_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v___x_4230_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4231_ = l_Lean_MessageData_ofConstName(v_declName_4211_, v___x_4217_);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
v___x_4235_ = l_Lean_stringToMessageData(v_val_4229_);
v___x_4236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4236_);
lean_ctor_set(v___x_4237_, 1, v___x_4230_);
v___x_4238_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4237_, v___y_4219_, v___y_4220_);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
lean_dec(v___x_4228_);
lean_dec(v_declName_4211_);
v___x_4239_ = lean_box(0);
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
v___jp_4241_:
{
lean_object* v___x_4244_; lean_object* v_env_4245_; lean_object* v___x_4246_; lean_object* v_toEnvExtension_4247_; lean_object* v_asyncMode_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4244_ = lean_st_ref_get(v___y_4243_);
v_env_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc_ref(v_env_4245_);
lean_dec(v___x_4244_);
v___x_4246_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4247_ = lean_ctor_get(v___x_4246_, 0);
v_asyncMode_4248_ = lean_ctor_get(v_toEnvExtension_4247_, 2);
v___x_4249_ = lean_box(0);
v___x_4250_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4209_, v___x_4246_, v_env_4245_, v_asyncMode_4248_, v___x_4249_, v___x_4217_);
v___x_4251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4250_, v_declName_4211_);
lean_dec(v___x_4250_);
if (lean_obj_tag(v___x_4251_) == 1)
{
lean_object* v_val_4252_; 
v_val_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_val_4252_);
lean_dec_ref_known(v___x_4251_, 1);
if (lean_obj_tag(v_val_4252_) == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec_ref_known(v_val_4252_, 5);
lean_dec(v___x_4208_);
v___x_4253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__1___closed__1);
v___x_4254_ = l_Lean_MessageData_ofConstName(v_declName_4211_, v___x_4217_);
v___x_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4253_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2_);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2574034933____hygCtx___hyg_2__spec__0___redArg(v___x_4257_, v___y_4242_, v___y_4243_);
return v___x_4258_;
}
else
{
v___y_4219_ = v___y_4242_;
v___y_4220_ = v___y_4243_;
goto v___jp_4218_;
}
}
else
{
lean_dec(v___x_4251_);
v___y_4219_ = v___y_4242_;
v___y_4220_ = v___y_4243_;
goto v___jp_4218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object* v___x_4270_, lean_object* v___x_4271_, lean_object* v_catName_4272_, lean_object* v_declName_4273_, lean_object* v___builtIn_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
uint8_t v___builtIn_boxed_4278_; lean_object* v_res_4279_; 
v___builtIn_boxed_4278_ = lean_unbox(v___builtIn_4274_);
v_res_4279_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(v___x_4270_, v___x_4271_, v_catName_4272_, v_declName_4273_, v___builtIn_boxed_4278_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v_catName_4272_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics));
v___x_4285_ = l_Lean_Parser_registerParserAttributeHook(v___x_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object* v_a_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
return v_res_4287_;
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
