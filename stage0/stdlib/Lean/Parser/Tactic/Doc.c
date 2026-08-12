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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "` is itself an alternative for `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` is not a tactic (it is in the categor"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ies"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Invalid `["};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` attribute syntax"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 29, 168, 181, 197, 113, 106, 176)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 168, 115, 176, 65, 44, 32, 74)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 127, 150, 230, 147, 51, 9, 44)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(171, 201, 216, 96, 187, 41, 25, 8)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(150, 217, 225, 249, 92, 227, 115, 9)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 73, 235, 188, 43, 204, 182, 169)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 40, 120, 84, 223, 15, 213, 179)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 14, 153, 180, 178, 10, 178, 110)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 228, 109, 71, 114, 58, 146, 87)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__17_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 220, 235, 94, 119, 251, 240, 121)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__18_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 121, 233, 68, 41, 52, 222, 209)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__19_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 103, 238, 221, 135, 73, 246, 74)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__20_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 42, 205, 170, 76, 149, 101, 166)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__21_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 231, 66, 168, 91, 162, 207, 65)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(710499956) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(132, 168, 224, 4, 116, 200, 36, 20)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__23_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 185, 77, 24, 123, 10, 110, 133)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__25_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 67, 140, 101, 31, 178, 245, 191)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__27_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(190, 125, 37, 177, 215, 25, 59, 117)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 120, .m_data = "Register a tactic parser as an alternative form of an existing tactic, so they can be grouped together in documentation."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__28_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__29_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__30_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2;
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
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__11_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1176478476) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(6, 145, 207, 84, 40, 68, 96, 133)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 222, 3, 19, 240, 88, 68, 38)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 217, 170, 202, 224, 178, 78, 10)}};
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
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0_value;
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
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "The tactic `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` already has the custom name `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "` is defined in an imported module, but custom names can only be added in the tactic's defining module."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is defined in `"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "`, but custom names can only be added in the tactic's defining module."};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__12_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_name"};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 250, 159, 49, 179, 121, 155, 115)}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__value)} };
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
return v___x_7_;
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
size_t v_x_353__boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_x_353__boxed_38_ = lean_unbox_usize(v_x_36_);
lean_dec(v_x_36_);
v_res_39_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_35_, v_x_353__boxed_38_, v_x_37_);
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
size_t v_x_428__boxed_98_; lean_object* v_res_99_; 
v_x_428__boxed_98_ = lean_unbox_usize(v_x_96_);
lean_dec(v_x_96_);
v_res_99_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_95_, v_x_428__boxed_98_, v_x_97_);
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
lean_object* v___x_116_; lean_object* v_ext_117_; lean_object* v_toEnvExtension_118_; lean_object* v_asyncMode_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_categories_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_116_ = l_Lean_Parser_parserExtension;
v_ext_117_ = lean_ctor_get(v___x_116_, 1);
v_toEnvExtension_118_ = lean_ctor_get(v_ext_117_, 0);
v_asyncMode_119_ = lean_ctor_get(v_toEnvExtension_118_, 2);
v___x_120_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_121_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_120_, v___x_116_, v_env_114_, v_asyncMode_119_);
v_categories_122_ = lean_ctor_get(v___x_121_, 2);
lean_inc_ref(v_categories_122_);
lean_dec(v___x_121_);
v___x_123_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_124_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_categories_122_, v___x_123_);
lean_dec_ref(v_categories_122_);
if (lean_obj_tag(v___x_124_) == 1)
{
lean_object* v_val_125_; lean_object* v_kinds_126_; uint8_t v___x_127_; 
v_val_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v___x_124_, 1);
v_kinds_126_ = lean_ctor_get(v_val_125_, 1);
lean_inc_ref(v_kinds_126_);
lean_dec(v_val_125_);
v___x_127_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_126_, v_kind_115_);
lean_dec_ref(v_kinds_126_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec(v___x_124_);
v___x_128_ = 0;
return v___x_128_;
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
size_t v_x_532__boxed_159_; lean_object* v_res_160_; 
v_x_532__boxed_159_ = lean_unbox_usize(v_x_157_);
lean_dec(v_x_157_);
v_res_160_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(v_00_u03b2_155_, v_x_156_, v_x_532__boxed_159_, v_x_158_);
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
size_t v_x_543__boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_x_543__boxed_170_ = lean_unbox_usize(v_x_168_);
lean_dec(v_x_168_);
v_res_171_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(v_00_u03b2_166_, v_x_167_, v_x_543__boxed_170_, v_x_169_);
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
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_388_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object* v_init_391_, lean_object* v_t_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_391_, v_t_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_394_, lean_object* v_t_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(v_init_394_, v_t_395_);
lean_dec(v_t_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object* v_n_397_, lean_object* v_as_398_, lean_object* v_lo_399_, lean_object* v_hi_400_, lean_object* v_w_401_, lean_object* v_hlo_402_, lean_object* v_hhi_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_397_, v_as_398_, v_lo_399_, v_hi_400_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_405_, lean_object* v_as_406_, lean_object* v_lo_407_, lean_object* v_hi_408_, lean_object* v_w_409_, lean_object* v_hlo_410_, lean_object* v_hhi_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(v_n_405_, v_as_406_, v_lo_407_, v_hi_408_, v_w_409_, v_hlo_410_, v_hhi_411_);
lean_dec(v_hi_408_);
lean_dec(v_n_405_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_413_, lean_object* v_lo_414_, lean_object* v_hi_415_, lean_object* v_hhi_416_, lean_object* v_pivot_417_, lean_object* v_as_418_, lean_object* v_i_419_, lean_object* v_k_420_, lean_object* v_ilo_421_, lean_object* v_ik_422_, lean_object* v_w_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_415_, v_pivot_417_, v_as_418_, v_i_419_, v_k_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_425_, lean_object* v_lo_426_, lean_object* v_hi_427_, lean_object* v_hhi_428_, lean_object* v_pivot_429_, lean_object* v_as_430_, lean_object* v_i_431_, lean_object* v_k_432_, lean_object* v_ilo_433_, lean_object* v_ik_434_, lean_object* v_w_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(v_n_425_, v_lo_426_, v_hi_427_, v_hhi_428_, v_pivot_429_, v_as_430_, v_i_431_, v_k_432_, v_ilo_433_, v_ik_434_, v_w_435_);
lean_dec_ref(v_pivot_429_);
lean_dec(v_hi_427_);
lean_dec(v_lo_426_);
lean_dec(v_n_425_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object* v_as_437_, lean_object* v_k_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_m_443_; lean_object* v_a_444_; uint8_t v___x_445_; 
v___x_441_ = lean_nat_add(v_x_439_, v_x_440_);
v___x_442_ = lean_unsigned_to_nat(1u);
v_m_443_ = lean_nat_shiftr(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v_a_444_ = lean_array_fget_borrowed(v_as_437_, v_m_443_);
v___x_445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_444_, v_k_438_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
lean_dec(v_x_440_);
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_438_, v_a_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v_m_443_);
lean_dec(v_x_439_);
lean_inc(v_a_444_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_a_444_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_m_443_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_nat_sub(v_m_443_, v___x_442_);
lean_dec(v_m_443_);
v___x_451_ = lean_nat_dec_lt(v___x_450_, v_x_439_);
if (v___x_451_ == 0)
{
v_x_440_ = v___x_450_;
goto _start;
}
else
{
lean_object* v___x_453_; 
lean_dec(v___x_450_);
lean_dec(v_x_439_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_m_443_);
lean_dec(v_x_439_);
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
lean_dec(v_x_439_);
v___x_455_ = lean_nat_add(v_m_443_, v___x_442_);
lean_dec(v_m_443_);
v___x_456_ = lean_nat_dec_le(v___x_455_, v_x_440_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_455_);
lean_dec(v_x_440_);
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
v_x_439_ = v___x_455_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object* v_as_459_, lean_object* v_k_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_459_, v_k_460_, v_x_461_, v_x_462_);
lean_dec_ref(v_k_460_);
lean_dec_ref(v_as_459_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object* v_env_464_, lean_object* v_tac_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_box(1);
v___x_467_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_464_, v_tac_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; lean_object* v_toEnvExtension_469_; lean_object* v_asyncMode_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_468_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_469_ = lean_ctor_get(v___x_468_, 0);
v_asyncMode_470_ = lean_ctor_get(v_toEnvExtension_469_, 2);
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_466_, v___x_468_, v_env_464_, v_asyncMode_470_, v___x_471_);
v___x_473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_472_, v_tac_465_);
lean_dec(v_tac_465_);
lean_dec(v___x_472_);
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_val_474_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_467_, 1);
v___x_475_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v___x_476_ = 0;
v___x_477_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_466_, v___x_475_, v_env_464_, v_val_474_, v___x_476_);
lean_dec(v_val_474_);
lean_dec_ref(v_env_464_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_array_get_size(v___x_477_);
v___x_480_ = lean_nat_dec_lt(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v___x_477_);
lean_dec(v_tac_465_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_sub(v___x_479_, v___x_482_);
v___x_484_ = lean_nat_dec_le(v___x_478_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec(v___x_483_);
lean_dec_ref(v___x_477_);
lean_dec(v_tac_465_);
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_tac_465_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v___x_477_, v___x_487_, v___x_478_, v___x_483_);
lean_dec_ref_known(v___x_487_, 2);
lean_dec_ref(v___x_477_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = lean_box(0);
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_val_490_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v___x_488_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_snd_494_; lean_object* v___x_496_; 
v_snd_494_ = lean_ctor_get(v_val_490_, 1);
lean_inc(v_snd_494_);
lean_dec(v_val_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_snd_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_snd_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(lean_object* v_as_499_, lean_object* v_k_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_499_, v_k_500_, v_x_501_, v_x_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___boxed(lean_object* v_as_505_, lean_object* v_k_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(v_as_505_, v_k_506_, v_x_507_, v_x_508_, v_x_509_);
lean_dec_ref(v_k_506_);
lean_dec_ref(v_as_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0(lean_object* v_toPure_511_, lean_object* v_____do__lift_512_){
_start:
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v_____do__lift_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v_____do__lift_512_);
v___x_514_ = lean_apply_2(v_toPure_511_, lean_box(0), v_a_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(lean_object* v_tac_515_, lean_object* v_toPure_516_, lean_object* v_a_517_, lean_object* v_b_518_, lean_object* v_c_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_name_eq(v_b_518_, v_tac_515_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_a_517_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_c_519_);
v___x_522_ = lean_apply_2(v_toPure_516_, lean_box(0), v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_NameSet_insert(v_c_519_, v_a_517_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
v___x_525_ = lean_apply_2(v_toPure_516_, lean_box(0), v___x_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed(lean_object* v_tac_526_, lean_object* v_toPure_527_, lean_object* v_a_528_, lean_object* v_b_529_, lean_object* v_c_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(v_tac_526_, v_toPure_527_, v_a_528_, v_b_529_, v_c_530_);
lean_dec(v_b_529_);
lean_dec(v_tac_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(lean_object* v_tac_532_, lean_object* v_toPure_533_, lean_object* v_a_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_fst_537_; lean_object* v_snd_538_; uint8_t v___x_539_; 
v_fst_537_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v_a_534_, 1);
lean_inc(v_snd_538_);
lean_dec_ref(v_a_534_);
v___x_539_ = lean_name_eq(v_snd_538_, v_tac_532_);
lean_dec(v_snd_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v_fst_537_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___y_536_);
v___x_541_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_540_);
return v___x_541_;
}
else
{
lean_object* v_found_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_found_542_ = l_Lean_NameSet_insert(v___y_536_, v_fst_537_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_found_542_);
v___x_544_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed(lean_object* v_tac_545_, lean_object* v_toPure_546_, lean_object* v_a_547_, lean_object* v_x_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(v_tac_545_, v_toPure_546_, v_a_547_, v_x_548_, v___y_549_);
lean_dec(v_tac_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3(lean_object* v_toPure_551_, lean_object* v_____s_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_____s_552_);
v___x_554_ = lean_apply_2(v_toPure_551_, lean_box(0), v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4(lean_object* v_inst_555_, lean_object* v___f_556_, lean_object* v_toBind_557_, lean_object* v___f_558_, lean_object* v_a_559_, lean_object* v_x_560_, lean_object* v___y_561_){
_start:
{
size_t v_sz_562_; size_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_sz_562_ = lean_array_size(v_a_559_);
v___x_563_ = ((size_t)0ULL);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_555_, v_a_559_, v___f_556_, v_sz_562_, v___x_563_, v___y_561_);
v___x_565_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v___x_564_, v___f_558_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5(lean_object* v_toPure_566_, lean_object* v_____s_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_apply_2(v_toPure_566_, lean_box(0), v_____s_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object* v___x_569_, lean_object* v_toEnvExtension_570_, lean_object* v_env_571_, lean_object* v_asyncMode_572_, lean_object* v___x_573_, lean_object* v_inst_574_, lean_object* v___f_575_, lean_object* v_toBind_576_, lean_object* v___f_577_, lean_object* v_____s_578_){
_start:
{
lean_object* v___x_579_; lean_object* v_importedEntries_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_579_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_569_, v_toEnvExtension_570_, v_env_571_, v_asyncMode_572_, v___x_573_);
v_importedEntries_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_importedEntries_580_);
lean_dec(v___x_579_);
v_sz_581_ = lean_array_size(v_importedEntries_580_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_574_, v_importedEntries_580_, v___f_575_, v_sz_581_, v___x_582_, v_____s_578_);
v___x_584_ = lean_apply_4(v_toBind_576_, lean_box(0), lean_box(0), v___x_583_, v___f_577_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object* v___x_585_, lean_object* v_toEnvExtension_586_, lean_object* v_env_587_, lean_object* v_asyncMode_588_, lean_object* v___x_589_, lean_object* v_inst_590_, lean_object* v___f_591_, lean_object* v_toBind_592_, lean_object* v___f_593_, lean_object* v_____s_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(v___x_585_, v_toEnvExtension_586_, v_env_587_, v_asyncMode_588_, v___x_589_, v_inst_590_, v___f_591_, v_toBind_592_, v___f_593_, v_____s_594_);
lean_dec(v_asyncMode_588_);
lean_dec_ref(v_toEnvExtension_586_);
lean_dec_ref(v___x_585_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object* v___x_596_, lean_object* v_inst_597_, lean_object* v___f_598_, lean_object* v_toBind_599_, lean_object* v___f_600_, lean_object* v___x_601_, lean_object* v___f_602_, lean_object* v___f_603_, lean_object* v_env_604_){
_start:
{
lean_object* v___x_605_; lean_object* v_toEnvExtension_606_; lean_object* v_asyncMode_607_; lean_object* v_found_608_; lean_object* v___x_609_; lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_605_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_606_ = lean_ctor_get(v___x_605_, 0);
v_asyncMode_607_ = lean_ctor_get(v_toEnvExtension_606_, 2);
v_found_608_ = l_Lean_NameSet_empty;
v___x_609_ = lean_box(0);
lean_inc_n(v_toBind_599_, 2);
lean_inc_ref(v_inst_597_);
lean_inc(v_asyncMode_607_);
lean_inc_ref(v_env_604_);
lean_inc_ref(v_toEnvExtension_606_);
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_610_, 0, v___x_596_);
lean_closure_set(v___f_610_, 1, v_toEnvExtension_606_);
lean_closure_set(v___f_610_, 2, v_env_604_);
lean_closure_set(v___f_610_, 3, v_asyncMode_607_);
lean_closure_set(v___f_610_, 4, v___x_609_);
lean_closure_set(v___f_610_, 5, v_inst_597_);
lean_closure_set(v___f_610_, 6, v___f_598_);
lean_closure_set(v___f_610_, 7, v_toBind_599_);
lean_closure_set(v___f_610_, 8, v___f_600_);
v___x_611_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_601_, v___x_605_, v_env_604_, v_asyncMode_607_, v___x_609_);
v___x_612_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_597_, v___f_602_, v_found_608_, v___x_611_);
v___x_613_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_612_, v___f_603_);
v___x_614_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_613_, v___f_610_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_box(1);
v___x_616_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_tac_619_){
_start:
{
lean_object* v_toApplicative_620_; lean_object* v_toBind_621_; lean_object* v_getEnv_622_; lean_object* v_toPure_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_633_; 
v_toApplicative_620_ = lean_ctor_get(v_inst_617_, 0);
v_toBind_621_ = lean_ctor_get(v_inst_617_, 1);
lean_inc_n(v_toBind_621_, 3);
v_getEnv_622_ = lean_ctor_get(v_inst_618_, 0);
lean_inc(v_getEnv_622_);
lean_dec_ref(v_inst_618_);
v_toPure_623_ = lean_ctor_get(v_toApplicative_620_, 1);
v___x_624_ = lean_box(1);
v___x_625_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_623_, 5);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_626_, 0, v_toPure_623_);
lean_inc(v_tac_619_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_627_, 0, v_tac_619_);
lean_closure_set(v___f_627_, 1, v_toPure_623_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_628_, 0, v_tac_619_);
lean_closure_set(v___f_628_, 1, v_toPure_623_);
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_629_, 0, v_toPure_623_);
lean_inc_ref(v_inst_617_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4), 7, 4);
lean_closure_set(v___f_630_, 0, v_inst_617_);
lean_closure_set(v___f_630_, 1, v___f_628_);
lean_closure_set(v___f_630_, 2, v_toBind_621_);
lean_closure_set(v___f_630_, 3, v___f_629_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5), 2, 1);
lean_closure_set(v___f_631_, 0, v_toPure_623_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7), 9, 8);
lean_closure_set(v___f_632_, 0, v___x_625_);
lean_closure_set(v___f_632_, 1, v_inst_617_);
lean_closure_set(v___f_632_, 2, v___f_630_);
lean_closure_set(v___f_632_, 3, v_toBind_621_);
lean_closure_set(v___f_632_, 4, v___f_631_);
lean_closure_set(v___f_632_, 5, v___x_624_);
lean_closure_set(v___f_632_, 6, v___f_627_);
lean_closure_set(v___f_632_, 7, v___f_626_);
v___x_633_ = lean_apply_4(v_toBind_621_, lean_box(0), lean_box(0), v_getEnv_622_, v___f_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object* v_m_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_tac_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Parser_Tactic_Doc_aliases___redArg(v_inst_635_, v_inst_636_, v_tac_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_639_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
lean_ctor_set(v___x_644_, 3, v___x_643_);
lean_ctor_set(v___x_644_, 4, v___x_642_);
lean_ctor_set(v___x_644_, 5, v___x_642_);
lean_ctor_set(v___x_644_, 6, v___x_642_);
lean_ctor_set(v___x_644_, 7, v___x_642_);
lean_ctor_set(v___x_644_, 8, v___x_642_);
lean_ctor_set(v___x_644_, 9, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(32u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = ((size_t)5ULL);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_unsigned_to_nat(32u);
v___x_651_ = lean_mk_empty_array_with_capacity(v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_649_);
lean_ctor_set(v___x_653_, 3, v___x_649_);
lean_ctor_set_usize(v___x_653_, 4, v___x_648_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_box(1);
v___x_655_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_656_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v_env_663_; lean_object* v_options_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_662_ = lean_st_ref_get(v___y_660_);
v_env_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_env_663_);
lean_dec(v___x_662_);
v_options_664_ = lean_ctor_get(v___y_659_, 2);
v___x_665_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_666_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_664_);
v___x_667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_667_, 0, v_env_663_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
lean_ctor_set(v___x_667_, 2, v___x_666_);
lean_ctor_set(v___x_667_, 3, v_options_664_);
v___x_668_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v_msgData_658_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msgData_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_ref_679_; lean_object* v___x_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_ref_679_ = lean_ctor_get(v___y_676_, 5);
v___x_680_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_675_, v___y_676_, v___y_677_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_689_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_inc(v_ref_679_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_ref_679_);
lean_ctor_set(v___x_685_, 1, v_a_681_);
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 1);
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_694_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_name_701_, lean_object* v_decl_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_706_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_707_ = l_Lean_MessageData_ofName(v_name_701_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_710_, v___y_703_, v___y_704_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_name_712_, lean_object* v_decl_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_name_712_, v_decl_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v_decl_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_decl_718_, lean_object* v_x_719_, lean_object* v_____s_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_snd_724_; lean_object* v_fst_725_; lean_object* v_kinds_726_; uint8_t v___x_727_; 
v_snd_724_ = lean_ctor_get(v_x_719_, 1);
lean_inc(v_snd_724_);
v_fst_725_ = lean_ctor_get(v_x_719_, 0);
lean_inc(v_fst_725_);
lean_dec_ref(v_x_719_);
v_kinds_726_ = lean_ctor_get(v_snd_724_, 1);
lean_inc_ref(v_kinds_726_);
lean_dec(v_snd_724_);
v___x_727_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_726_, v_decl_718_);
lean_dec_ref(v_kinds_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_fst_725_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_____s_720_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_array_push(v_____s_720_, v_fst_725_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_decl_733_, lean_object* v_x_734_, lean_object* v_____s_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_decl_733_, v_x_734_, v_____s_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v_decl_733_);
return v_res_739_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(size_t v_sz_743_, size_t v_i_744_, lean_object* v_bs_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_usize_dec_lt(v_i_744_, v_sz_743_);
if (v___x_746_ == 0)
{
return v_bs_745_;
}
else
{
lean_object* v_v_747_; lean_object* v___x_748_; lean_object* v_bs_x27_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_v_747_ = lean_array_uget(v_bs_745_, v_i_744_);
v___x_748_ = lean_unsigned_to_nat(0u);
v_bs_x27_749_ = lean_array_uset(v_bs_745_, v_i_744_, v___x_748_);
v___x_750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_751_ = l_Lean_MessageData_ofName(v_v_747_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_750_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_744_, v___x_754_);
v___x_756_ = lean_array_uset(v_bs_x27_749_, v_i_744_, v___x_753_);
v_i_744_ = v___x_755_;
v_bs_745_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___boxed(lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_bs_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_boxed_761_, v_i_boxed_762_, v_bs_760_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(lean_object* v_name_773_, uint8_t v_kind_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___y_784_; 
v___x_778_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1);
v___x_779_ = l_Lean_MessageData_ofName(v_name_773_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
switch(v_kind_774_)
{
case 0:
{
lean_object* v___x_791_; 
v___x_791_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4));
v___y_784_ = v___x_791_;
goto v___jp_783_;
}
case 1:
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5));
v___y_784_ = v___x_792_;
goto v___jp_783_;
}
default: 
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6));
v___y_784_ = v___x_793_;
goto v___jp_783_;
}
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v___y_784_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___y_784_);
v___x_786_ = l_Lean_MessageData_ofFormat(v___x_785_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_789_, v___y_775_, v___y_776_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___boxed(lean_object* v_name_794_, lean_object* v_kind_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v_kind_boxed_799_; lean_object* v_res_800_; 
v_kind_boxed_799_ = lean_unbox(v_kind_795_);
v_res_800_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_794_, v_kind_boxed_799_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(lean_object* v_f_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_i_804_, lean_object* v_acc_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_array_get_size(v_keys_802_);
v___x_810_ = lean_nat_dec_lt(v_i_804_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_i_804_);
lean_dec_ref(v_f_801_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v_acc_805_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
else
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v___x_815_; 
v_k_813_ = lean_array_fget_borrowed(v_keys_802_, v_i_804_);
v_v_814_ = lean_array_fget_borrowed(v_vals_803_, v_i_804_);
lean_inc_ref(v_f_801_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v_v_814_);
lean_inc(v_k_813_);
v___x_815_ = lean_apply_6(v_f_801_, v_acc_805_, v_k_813_, v_v_814_, v___y_806_, v___y_807_, lean_box(0));
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
if (lean_obj_tag(v_a_816_) == 0)
{
lean_dec_ref_known(v_a_816_, 1);
lean_dec(v_i_804_);
lean_dec_ref(v_f_801_);
return v___x_815_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref_known(v___x_815_, 1);
v_a_817_ = lean_ctor_get(v_a_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v_a_816_, 1);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_i_804_, v___x_818_);
lean_dec(v_i_804_);
v_i_804_ = v___x_819_;
v_acc_805_ = v_a_817_;
goto _start;
}
}
else
{
lean_dec(v_i_804_);
lean_dec_ref(v_f_801_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_f_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_i_824_, lean_object* v_acc_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_821_, v_keys_822_, v_vals_823_, v_i_824_, v_acc_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec_ref(v_vals_823_);
lean_dec_ref(v_keys_822_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_f_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
if (lean_obj_tag(v_x_831_) == 0)
{
lean_object* v_es_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_858_; 
v_es_836_ = lean_ctor_get(v_x_831_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_831_);
if (v_isSharedCheck_858_ == 0)
{
v___x_838_ = v_x_831_;
v_isShared_839_ = v_isSharedCheck_858_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_es_836_);
lean_dec(v_x_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_858_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_array_get_size(v_es_836_);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_es_836_);
lean_dec_ref(v_f_830_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 0, v_x_832_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_x_832_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_le(v___x_841_, v___x_841_);
if (v___x_847_ == 0)
{
if (v___x_842_ == 0)
{
lean_object* v___x_849_; 
lean_dec_ref(v_es_836_);
lean_dec_ref(v_f_830_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 0, v_x_832_);
v___x_849_ = v___x_838_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_x_832_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
else
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
lean_del_object(v___x_838_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_of_nat(v___x_841_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_830_, v_es_836_, v___x_852_, v___x_853_, v_x_832_, v___y_833_, v___y_834_);
lean_dec_ref(v_es_836_);
return v___x_854_;
}
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
lean_del_object(v___x_838_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_of_nat(v___x_841_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_830_, v_es_836_, v___x_855_, v___x_856_, v_x_832_, v___y_833_, v___y_834_);
lean_dec_ref(v_es_836_);
return v___x_857_;
}
}
}
}
else
{
lean_object* v_ks_859_; lean_object* v_vs_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_ks_859_ = lean_ctor_get(v_x_831_, 0);
lean_inc_ref(v_ks_859_);
v_vs_860_ = lean_ctor_get(v_x_831_, 1);
lean_inc_ref(v_vs_860_);
lean_dec_ref_known(v_x_831_, 2);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_830_, v_ks_859_, v_vs_860_, v___x_861_, v_x_832_, v___y_833_, v___y_834_);
lean_dec_ref(v_vs_860_);
lean_dec_ref(v_ks_859_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(lean_object* v_f_863_, lean_object* v_as_864_, size_t v_i_865_, size_t v_stop_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_a_872_; lean_object* v___y_877_; uint8_t v___x_880_; 
v___x_880_ = lean_usize_dec_eq(v_i_865_, v_stop_866_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_array_uget_borrowed(v_as_864_, v_i_865_);
switch(lean_obj_tag(v___x_881_))
{
case 0:
{
lean_object* v_key_882_; lean_object* v_val_883_; lean_object* v___x_884_; 
v_key_882_ = lean_ctor_get(v___x_881_, 0);
v_val_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc_ref(v_f_863_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v_val_883_);
lean_inc(v_key_882_);
v___x_884_ = lean_apply_6(v_f_863_, v_b_867_, v_key_882_, v_val_883_, v___y_868_, v___y_869_, lean_box(0));
v___y_877_ = v___x_884_;
goto v___jp_876_;
}
case 1:
{
lean_object* v_node_885_; lean_object* v___x_886_; 
v_node_885_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_node_885_);
lean_inc_ref(v_f_863_);
v___x_886_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_863_, v_node_885_, v_b_867_, v___y_868_, v___y_869_);
v___y_877_ = v___x_886_;
goto v___jp_876_;
}
default: 
{
v_a_872_ = v_b_867_;
goto v___jp_871_;
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v_f_863_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_867_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_865_, v___x_873_);
v_i_865_ = v___x_874_;
v_b_867_ = v_a_872_;
goto _start;
}
v___jp_876_:
{
if (lean_obj_tag(v___y_877_) == 0)
{
lean_object* v_a_878_; 
v_a_878_ = lean_ctor_get(v___y_877_, 0);
if (lean_obj_tag(v_a_878_) == 0)
{
lean_dec_ref(v_f_863_);
return v___y_877_;
}
else
{
lean_object* v_a_879_; 
lean_inc_ref(v_a_878_);
lean_dec_ref_known(v___y_877_, 1);
v_a_879_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v_a_878_, 1);
v_a_872_ = v_a_879_;
goto v___jp_871_;
}
}
else
{
lean_dec_ref(v_f_863_);
return v___y_877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_f_889_, lean_object* v_as_890_, lean_object* v_i_891_, lean_object* v_stop_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_i_boxed_897_; size_t v_stop_boxed_898_; lean_object* v_res_899_; 
v_i_boxed_897_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_stop_boxed_898_ = lean_unbox_usize(v_stop_892_);
lean_dec(v_stop_892_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_889_, v_as_890_, v_i_boxed_897_, v_stop_boxed_898_, v_b_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_as_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_900_, v_x_901_, v_x_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_f_907_, lean_object* v_s_908_, lean_object* v_a_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_a_909_);
lean_ctor_set(v___x_914_, 1, v_b_910_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
v___x_915_ = lean_apply_5(v_f_907_, v___x_914_, v_s_908_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_942_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_942_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_a_916_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_a_920_ = lean_ctor_get(v_a_916_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_930_ == 0)
{
v___x_922_ = v_a_916_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v_a_916_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_925_);
v___x_927_ = v___x_918_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_941_; 
v_a_931_ = lean_ctor_get(v_a_916_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_941_ == 0)
{
v___x_933_ = v_a_916_;
v_isShared_934_ = v_isSharedCheck_941_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_a_916_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_941_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_940_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_936_);
v___x_938_ = v___x_918_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_915_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_915_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_f_951_, lean_object* v_s_952_, lean_object* v_a_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(v_f_951_, v_s_952_, v_a_953_, v_b_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(lean_object* v_map_959_, lean_object* v_init_960_, lean_object* v_f_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_965_, 0, v_f_961_);
lean_inc_ref(v_map_959_);
v___x_966_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v___f_965_, v_map_959_, v_init_960_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_a_971_; lean_object* v___x_973_; 
v_a_971_ = lean_ctor_get(v_a_967_, 0);
lean_inc(v_a_971_);
lean_dec(v_a_967_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_a_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_966_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_966_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_map_984_, lean_object* v_init_985_, lean_object* v_f_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_984_, v_init_985_, v_f_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v_map_984_);
return v_res_990_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_991_; double v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_float_of_nat(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_cls_996_, lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_ref_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1047_; 
v_ref_1001_ = lean_ctor_get(v___y_998_, 5);
v___x_1002_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_997_, v___y_998_, v___y_999_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1047_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1047_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v_traceState_1008_; lean_object* v_env_1009_; lean_object* v_nextMacroScope_1010_; lean_object* v_ngen_1011_; lean_object* v_auxDeclNGen_1012_; lean_object* v_cache_1013_; lean_object* v_messages_1014_; lean_object* v_infoState_1015_; lean_object* v_snapshotTasks_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1046_; 
v___x_1007_ = lean_st_ref_take(v___y_999_);
v_traceState_1008_ = lean_ctor_get(v___x_1007_, 4);
v_env_1009_ = lean_ctor_get(v___x_1007_, 0);
v_nextMacroScope_1010_ = lean_ctor_get(v___x_1007_, 1);
v_ngen_1011_ = lean_ctor_get(v___x_1007_, 2);
v_auxDeclNGen_1012_ = lean_ctor_get(v___x_1007_, 3);
v_cache_1013_ = lean_ctor_get(v___x_1007_, 5);
v_messages_1014_ = lean_ctor_get(v___x_1007_, 6);
v_infoState_1015_ = lean_ctor_get(v___x_1007_, 7);
v_snapshotTasks_1016_ = lean_ctor_get(v___x_1007_, 8);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1018_ = v___x_1007_;
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snapshotTasks_1016_);
lean_inc(v_infoState_1015_);
lean_inc(v_messages_1014_);
lean_inc(v_cache_1013_);
lean_inc(v_traceState_1008_);
lean_inc(v_auxDeclNGen_1012_);
lean_inc(v_ngen_1011_);
lean_inc(v_nextMacroScope_1010_);
lean_inc(v_env_1009_);
lean_dec(v___x_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint64_t v_tid_1020_; lean_object* v_traces_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_tid_1020_ = lean_ctor_get_uint64(v_traceState_1008_, sizeof(void*)*1);
v_traces_1021_ = lean_ctor_get(v_traceState_1008_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_traceState_1008_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_traceState_1008_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_traces_1021_);
lean_dec(v_traceState_1008_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; double v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0);
v___x_1027_ = 0;
v___x_1028_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1029_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1029_, 0, v_cls_996_);
lean_ctor_set(v___x_1029_, 1, v___x_1025_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
lean_ctor_set_float(v___x_1029_, sizeof(void*)*3, v___x_1026_);
lean_ctor_set_float(v___x_1029_, sizeof(void*)*3 + 8, v___x_1026_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*3 + 16, v___x_1027_);
v___x_1030_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2));
v___x_1031_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v_a_1003_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
lean_inc(v_ref_1001_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_ref_1001_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_PersistentArray_push___redArg(v_traces_1021_, v___x_1032_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1033_);
v___x_1035_ = v___x_1023_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1033_);
lean_ctor_set_uint64(v_reuseFailAlloc_1044_, sizeof(void*)*1, v_tid_1020_);
v___x_1035_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 4, v___x_1035_);
v___x_1037_ = v___x_1018_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_env_1009_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_nextMacroScope_1010_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_ngen_1011_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_auxDeclNGen_1012_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v_cache_1013_);
lean_ctor_set(v_reuseFailAlloc_1043_, 6, v_messages_1014_);
lean_ctor_set(v_reuseFailAlloc_1043_, 7, v_infoState_1015_);
lean_ctor_set(v_reuseFailAlloc_1043_, 8, v_snapshotTasks_1016_);
v___x_1037_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = lean_st_ref_set(v___y_999_, v___x_1037_);
v___x_1039_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1039_);
v___x_1041_ = v___x_1005_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_cls_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1048_, v_msg_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_keys_1054_, lean_object* v_i_1055_, lean_object* v_k_1056_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_array_get_size(v_keys_1054_);
v___x_1058_ = lean_nat_dec_lt(v_i_1055_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec(v_i_1055_);
return v___x_1058_;
}
else
{
lean_object* v_k_x27_1059_; uint8_t v___x_1060_; 
v_k_x27_1059_ = lean_array_fget_borrowed(v_keys_1054_, v_i_1055_);
v___x_1060_ = l_Lean_instBEqExtraModUse_beq(v_k_1056_, v_k_x27_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_i_1055_, v___x_1061_);
lean_dec(v_i_1055_);
v_i_1055_ = v___x_1062_;
goto _start;
}
else
{
lean_dec(v_i_1055_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_keys_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1064_, v_i_1065_, v_k_1066_);
lean_dec_ref(v_k_1066_);
lean_dec_ref(v_keys_1064_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_x_1069_, size_t v_x_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
lean_object* v_es_1072_; lean_object* v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v_j_1076_; lean_object* v___x_1077_; 
v_es_1072_ = lean_ctor_get(v_x_1069_, 0);
v___x_1073_ = lean_box(2);
v___x_1074_ = ((size_t)31ULL);
v___x_1075_ = lean_usize_land(v_x_1070_, v___x_1074_);
v_j_1076_ = lean_usize_to_nat(v___x_1075_);
v___x_1077_ = lean_array_get_borrowed(v___x_1073_, v_es_1072_, v_j_1076_);
lean_dec(v_j_1076_);
switch(lean_obj_tag(v___x_1077_))
{
case 0:
{
lean_object* v_key_1078_; uint8_t v___x_1079_; 
v_key_1078_ = lean_ctor_get(v___x_1077_, 0);
v___x_1079_ = l_Lean_instBEqExtraModUse_beq(v_x_1071_, v_key_1078_);
return v___x_1079_;
}
case 1:
{
lean_object* v_node_1080_; size_t v___x_1081_; size_t v___x_1082_; 
v_node_1080_ = lean_ctor_get(v___x_1077_, 0);
v___x_1081_ = ((size_t)5ULL);
v___x_1082_ = lean_usize_shift_right(v_x_1070_, v___x_1081_);
v_x_1069_ = v_node_1080_;
v_x_1070_ = v___x_1082_;
goto _start;
}
default: 
{
uint8_t v___x_1084_; 
v___x_1084_ = 0;
return v___x_1084_;
}
}
}
else
{
lean_object* v_ks_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_ks_1085_ = lean_ctor_get(v_x_1069_, 0);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_ks_1085_, v___x_1086_, v_x_1071_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
size_t v_x_12204__boxed_1091_; uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_x_12204__boxed_1091_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_res_1092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1088_, v_x_12204__boxed_1091_, v_x_1090_);
lean_dec_ref(v_x_1090_);
lean_dec_ref(v_x_1088_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint64_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = l_Lean_instHashableExtraModUse_hash(v_x_1095_);
v___x_1097_ = lean_uint64_to_usize(v___x_1096_);
v___x_1098_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1094_, v___x_1097_, v_x_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1099_, v_x_1100_);
lean_dec_ref(v_x_1100_);
lean_dec_ref(v_x_1099_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1));
v___x_1106_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0));
v___x_1107_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15(void){
_start:
{
lean_object* v_cls_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_cls_1127_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1128_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14));
v___x_1129_ = l_Lean_Name_append(v___x_1128_, v_cls_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_mod_1140_, uint8_t v_isMeta_1141_, lean_object* v_hint_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_env_1147_; uint8_t v_isExporting_1148_; lean_object* v___x_1149_; lean_object* v_env_1150_; lean_object* v___x_1151_; lean_object* v_entry_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1146_ = lean_st_ref_get(v___y_1144_);
v_env_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc_ref(v_env_1147_);
lean_dec(v___x_1146_);
v_isExporting_1148_ = lean_ctor_get_uint8(v_env_1147_, sizeof(void*)*8);
lean_dec_ref(v_env_1147_);
v___x_1149_ = lean_st_ref_get(v___y_1144_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_env_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2);
lean_inc(v_mod_1140_);
v_entry_1152_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1152_, 0, v_mod_1140_);
lean_ctor_set_uint8(v_entry_1152_, sizeof(void*)*1, v_isExporting_1148_);
lean_ctor_set_uint8(v_entry_1152_, sizeof(void*)*1 + 1, v_isMeta_1141_);
v___x_1153_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1154_ = lean_box(1);
v___x_1155_ = lean_box(0);
v___x_1182_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1151_, v___x_1153_, v_env_1150_, v___x_1154_, v___x_1155_);
v___x_1183_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_1182_, v_entry_1152_);
lean_dec(v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v_options_1184_; uint8_t v_hasTrace_1185_; 
v_options_1184_ = lean_ctor_get(v___y_1143_, 2);
v_hasTrace_1185_ = lean_ctor_get_uint8(v_options_1184_, sizeof(void*)*1);
if (v_hasTrace_1185_ == 0)
{
lean_dec(v_hint_1142_);
lean_dec(v_mod_1140_);
v___y_1157_ = v___y_1144_;
goto v___jp_1156_;
}
else
{
lean_object* v_inheritedTraceOptions_1186_; lean_object* v_cls_1187_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_inheritedTraceOptions_1186_ = lean_ctor_get(v___y_1143_, 13);
v_cls_1187_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1207_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15);
v___x_1208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1186_, v_options_1184_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_dec(v_hint_1142_);
lean_dec(v_mod_1140_);
v___y_1157_ = v___y_1144_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1209_; lean_object* v___y_1211_; 
v___x_1209_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17);
if (v_isExporting_1148_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22));
v___y_1211_ = v___x_1218_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23));
v___y_1211_ = v___x_1219_;
goto v___jp_1210_;
}
v___jp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_inc_ref(v___y_1211_);
v___x_1212_ = l_Lean_stringToMessageData(v___y_1211_);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1209_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
if (v_isMeta_1141_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20));
v___y_1194_ = v___x_1215_;
v___y_1195_ = v___x_1216_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1217_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21));
v___y_1194_ = v___x_1215_;
v___y_1195_ = v___x_1217_;
goto v___jp_1193_;
}
}
}
v___jp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1189_);
lean_ctor_set(v___x_1191_, 1, v___y_1190_);
v___x_1192_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1187_, v___x_1191_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref_known(v___x_1192_, 1);
v___y_1157_ = v___y_1144_;
goto v___jp_1156_;
}
else
{
lean_dec_ref_known(v_entry_1152_, 1);
return v___x_1192_;
}
}
v___jp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
lean_inc_ref(v___y_1195_);
v___x_1196_ = l_Lean_stringToMessageData(v___y_1195_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___y_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_MessageData_ofName(v_mod_1140_);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_Name_isAnonymous(v_hint_1142_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11);
v___x_1204_ = l_Lean_MessageData_ofName(v_hint_1142_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___y_1189_ = v___x_1201_;
v___y_1190_ = v___x_1205_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1206_; 
lean_dec(v_hint_1142_);
v___x_1206_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12);
v___y_1189_ = v___x_1201_;
v___y_1190_ = v___x_1206_;
goto v___jp_1188_;
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref_known(v_entry_1152_, 1);
lean_dec(v_hint_1142_);
lean_dec(v_mod_1140_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v_toEnvExtension_1159_; lean_object* v_env_1160_; lean_object* v_nextMacroScope_1161_; lean_object* v_ngen_1162_; lean_object* v_auxDeclNGen_1163_; lean_object* v_traceState_1164_; lean_object* v_messages_1165_; lean_object* v_infoState_1166_; lean_object* v_snapshotTasks_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1180_; 
v___x_1158_ = lean_st_ref_take(v___y_1157_);
v_toEnvExtension_1159_ = lean_ctor_get(v___x_1153_, 0);
v_env_1160_ = lean_ctor_get(v___x_1158_, 0);
v_nextMacroScope_1161_ = lean_ctor_get(v___x_1158_, 1);
v_ngen_1162_ = lean_ctor_get(v___x_1158_, 2);
v_auxDeclNGen_1163_ = lean_ctor_get(v___x_1158_, 3);
v_traceState_1164_ = lean_ctor_get(v___x_1158_, 4);
v_messages_1165_ = lean_ctor_get(v___x_1158_, 6);
v_infoState_1166_ = lean_ctor_get(v___x_1158_, 7);
v_snapshotTasks_1167_ = lean_ctor_get(v___x_1158_, 8);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1158_, 5);
lean_dec(v_unused_1181_);
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snapshotTasks_1167_);
lean_inc(v_infoState_1166_);
lean_inc(v_messages_1165_);
lean_inc(v_traceState_1164_);
lean_inc(v_auxDeclNGen_1163_);
lean_inc(v_ngen_1162_);
lean_inc(v_nextMacroScope_1161_);
lean_inc(v_env_1160_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_asyncMode_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v_asyncMode_1171_ = lean_ctor_get(v_toEnvExtension_1159_, 2);
v___x_1172_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1153_, v_env_1160_, v_entry_1152_, v_asyncMode_1171_, v___x_1155_);
v___x_1173_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 5, v___x_1173_);
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_nextMacroScope_1161_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_ngen_1162_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_auxDeclNGen_1163_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_traceState_1164_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_messages_1165_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_infoState_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_snapshotTasks_1167_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_st_ref_set(v___y_1157_, v___x_1175_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_mod_1222_, lean_object* v_isMeta_1223_, lean_object* v_hint_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v_isMeta_boxed_1228_; lean_object* v_res_1229_; 
v_isMeta_boxed_1228_ = lean_unbox(v_isMeta_1223_);
v_res_1229_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_mod_1222_, v_isMeta_boxed_1228_, v_hint_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(lean_object* v___x_1230_, lean_object* v_declName_1231_, lean_object* v_as_1232_, size_t v_sz_1233_, size_t v_i_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_lt(v_i_1234_, v_sz_1233_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_declName_1231_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_b_1235_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v_modules_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v_toImport_1246_; lean_object* v_module_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1241_ = l_Lean_Environment_header(v___x_1230_);
v_modules_1242_ = lean_ctor_get(v___x_1241_, 3);
lean_inc_ref(v_modules_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1244_ = lean_array_uget_borrowed(v_as_1232_, v_i_1234_);
v___x_1245_ = lean_array_get(v___x_1243_, v_modules_1242_, v_a_1244_);
lean_dec_ref(v_modules_1242_);
v_toImport_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_toImport_1246_);
lean_dec(v___x_1245_);
v_module_1247_ = lean_ctor_get(v_toImport_1246_, 0);
lean_inc(v_module_1247_);
lean_dec_ref(v_toImport_1246_);
v___x_1248_ = 0;
lean_inc(v_declName_1231_);
v___x_1249_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1247_, v___x_1248_, v_declName_1231_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; 
lean_dec_ref_known(v___x_1249_, 1);
v___x_1250_ = lean_box(0);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1234_, v___x_1251_);
v_i_1234_ = v___x_1252_;
v_b_1235_ = v___x_1250_;
goto _start;
}
else
{
lean_dec(v_declName_1231_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v___x_1254_, lean_object* v_declName_1255_, lean_object* v_as_1256_, lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
size_t v_sz_boxed_1263_; size_t v_i_boxed_1264_; lean_object* v_res_1265_; 
v_sz_boxed_1263_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1264_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v___x_1254_, v_declName_1255_, v_as_1256_, v_sz_boxed_1263_, v_i_boxed_1264_, v_b_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_as_1256_);
lean_dec_ref(v___x_1254_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
if (lean_obj_tag(v_x_1267_) == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
lean_object* v_key_1269_; lean_object* v_value_1270_; lean_object* v_tail_1271_; uint8_t v___x_1272_; 
v_key_1269_ = lean_ctor_get(v_x_1267_, 0);
v_value_1270_ = lean_ctor_get(v_x_1267_, 1);
v_tail_1271_ = lean_ctor_get(v_x_1267_, 2);
v___x_1272_ = lean_name_eq(v_key_1269_, v_a_1266_);
if (v___x_1272_ == 0)
{
v_x_1267_ = v_tail_1271_;
goto _start;
}
else
{
lean_object* v___x_1274_; 
lean_inc(v_value_1270_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_value_1270_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_a_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1275_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec(v_a_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(lean_object* v_m_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_buckets_1280_; lean_object* v___x_1281_; uint64_t v___y_1283_; 
v_buckets_1280_ = lean_ctor_get(v_m_1278_, 1);
v___x_1281_ = lean_array_get_size(v_buckets_1280_);
if (lean_obj_tag(v_a_1279_) == 0)
{
uint64_t v___x_1297_; 
v___x_1297_ = 1723ULL;
v___y_1283_ = v___x_1297_;
goto v___jp_1282_;
}
else
{
uint64_t v_hash_1298_; 
v_hash_1298_ = lean_ctor_get_uint64(v_a_1279_, sizeof(void*)*2);
v___y_1283_ = v_hash_1298_;
goto v___jp_1282_;
}
v___jp_1282_:
{
uint64_t v___x_1284_; uint64_t v___x_1285_; uint64_t v_fold_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1284_ = 32ULL;
v___x_1285_ = lean_uint64_shift_right(v___y_1283_, v___x_1284_);
v_fold_1286_ = lean_uint64_xor(v___y_1283_, v___x_1285_);
v___x_1287_ = 16ULL;
v___x_1288_ = lean_uint64_shift_right(v_fold_1286_, v___x_1287_);
v___x_1289_ = lean_uint64_xor(v_fold_1286_, v___x_1288_);
v___x_1290_ = lean_uint64_to_usize(v___x_1289_);
v___x_1291_ = lean_usize_of_nat(v___x_1281_);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_sub(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_usize_land(v___x_1290_, v___x_1293_);
v___x_1295_ = lean_array_uget_borrowed(v_buckets_1280_, v___x_1294_);
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1279_, v___x_1295_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg___boxed(lean_object* v_m_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_m_1299_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1));
v___x_1305_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0));
v___x_1306_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1305_, v___x_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(lean_object* v_declName_1309_, uint8_t v_isMeta_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v_env_1318_; lean_object* v___y_1320_; lean_object* v___x_1333_; 
v___x_1314_ = lean_st_ref_get(v___y_1312_);
v_env_1318_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref(v_env_1318_);
lean_dec(v___x_1314_);
v___x_1333_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1318_, v_declName_1309_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref(v_env_1318_);
lean_dec(v_declName_1309_);
goto v___jp_1315_;
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1335_; lean_object* v_modules_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = l_Lean_Environment_header(v_env_1318_);
v_modules_1336_ = lean_ctor_get(v___x_1335_, 3);
lean_inc_ref(v_modules_1336_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_array_get_size(v_modules_1336_);
v___x_1338_ = lean_nat_dec_lt(v_val_1334_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v_modules_1336_);
lean_dec(v_val_1334_);
lean_dec_ref(v_env_1318_);
lean_dec(v_declName_1309_);
goto v___jp_1315_;
}
else
{
lean_object* v___x_1339_; lean_object* v_env_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___y_1344_; 
v___x_1339_ = lean_st_ref_get(v___y_1312_);
v_env_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_env_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2);
v___x_1342_ = lean_array_fget(v_modules_1336_, v_val_1334_);
lean_dec(v_val_1334_);
lean_dec_ref(v_modules_1336_);
if (v_isMeta_1310_ == 0)
{
lean_dec_ref(v_env_1340_);
v___y_1344_ = v_isMeta_1310_;
goto v___jp_1343_;
}
else
{
uint8_t v___x_1355_; 
lean_inc(v_declName_1309_);
v___x_1355_ = l_Lean_isMarkedMeta(v_env_1340_, v_declName_1309_);
if (v___x_1355_ == 0)
{
v___y_1344_ = v_isMeta_1310_;
goto v___jp_1343_;
}
else
{
uint8_t v___x_1356_; 
v___x_1356_ = 0;
v___y_1344_ = v___x_1356_;
goto v___jp_1343_;
}
}
v___jp_1343_:
{
lean_object* v_toImport_1345_; lean_object* v_module_1346_; lean_object* v___x_1347_; 
v_toImport_1345_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_ref(v_toImport_1345_);
lean_dec(v___x_1342_);
v_module_1346_ = lean_ctor_get(v_toImport_1345_, 0);
lean_inc(v_module_1346_);
lean_dec_ref(v_toImport_1345_);
lean_inc(v_declName_1309_);
v___x_1347_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1346_, v___y_1344_, v_declName_1309_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = l_Lean_indirectModUseExt;
v___x_1349_ = lean_box(1);
v___x_1350_ = lean_box(0);
lean_inc_ref(v_env_1318_);
v___x_1351_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1341_, v___x_1348_, v_env_1318_, v___x_1349_, v___x_1350_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v___x_1351_, v_declName_1309_);
lean_dec(v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1353_; 
v___x_1353_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3));
v___y_1320_ = v___x_1353_;
goto v___jp_1319_;
}
else
{
lean_object* v_val_1354_; 
v_val_1354_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v___x_1352_, 1);
v___y_1320_ = v_val_1354_;
goto v___jp_1319_;
}
}
else
{
lean_dec_ref(v_env_1318_);
lean_dec(v_declName_1309_);
return v___x_1347_;
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(0);
v_sz_1322_ = lean_array_size(v___y_1320_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v_env_1318_, v_declName_1309_, v___y_1320_, v_sz_1322_, v___x_1323_, v___x_1321_, v___y_1311_, v___y_1312_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_env_1318_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1324_, 0);
lean_dec(v_unused_1332_);
v___x_1326_ = v___x_1324_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v___x_1324_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1321_);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1321_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___boxed(lean_object* v_declName_1357_, lean_object* v_isMeta_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v_isMeta_boxed_1362_; lean_object* v_res_1363_; 
v_isMeta_boxed_1362_ = lean_unbox(v_isMeta_1358_);
v_res_1363_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_declName_1357_, v_isMeta_boxed_1362_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_fileName_1369_; lean_object* v_fileMap_1370_; lean_object* v_options_1371_; lean_object* v_currRecDepth_1372_; lean_object* v_maxRecDepth_1373_; lean_object* v_ref_1374_; lean_object* v_currNamespace_1375_; lean_object* v_openDecls_1376_; lean_object* v_initHeartbeats_1377_; lean_object* v_maxHeartbeats_1378_; lean_object* v_quotContext_1379_; lean_object* v_currMacroScope_1380_; uint8_t v_diag_1381_; lean_object* v_cancelTk_x3f_1382_; uint8_t v_suppressElabErrors_1383_; lean_object* v_inheritedTraceOptions_1384_; lean_object* v_ref_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_fileName_1369_ = lean_ctor_get(v___y_1366_, 0);
v_fileMap_1370_ = lean_ctor_get(v___y_1366_, 1);
v_options_1371_ = lean_ctor_get(v___y_1366_, 2);
v_currRecDepth_1372_ = lean_ctor_get(v___y_1366_, 3);
v_maxRecDepth_1373_ = lean_ctor_get(v___y_1366_, 4);
v_ref_1374_ = lean_ctor_get(v___y_1366_, 5);
v_currNamespace_1375_ = lean_ctor_get(v___y_1366_, 6);
v_openDecls_1376_ = lean_ctor_get(v___y_1366_, 7);
v_initHeartbeats_1377_ = lean_ctor_get(v___y_1366_, 8);
v_maxHeartbeats_1378_ = lean_ctor_get(v___y_1366_, 9);
v_quotContext_1379_ = lean_ctor_get(v___y_1366_, 10);
v_currMacroScope_1380_ = lean_ctor_get(v___y_1366_, 11);
v_diag_1381_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*14);
v_cancelTk_x3f_1382_ = lean_ctor_get(v___y_1366_, 12);
v_suppressElabErrors_1383_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1384_ = lean_ctor_get(v___y_1366_, 13);
v_ref_1385_ = l_Lean_replaceRef(v_ref_1364_, v_ref_1374_);
lean_inc_ref(v_inheritedTraceOptions_1384_);
lean_inc(v_cancelTk_x3f_1382_);
lean_inc(v_currMacroScope_1380_);
lean_inc(v_quotContext_1379_);
lean_inc(v_maxHeartbeats_1378_);
lean_inc(v_initHeartbeats_1377_);
lean_inc(v_openDecls_1376_);
lean_inc(v_currNamespace_1375_);
lean_inc(v_maxRecDepth_1373_);
lean_inc(v_currRecDepth_1372_);
lean_inc_ref(v_options_1371_);
lean_inc_ref(v_fileMap_1370_);
lean_inc_ref(v_fileName_1369_);
v___x_1386_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1386_, 0, v_fileName_1369_);
lean_ctor_set(v___x_1386_, 1, v_fileMap_1370_);
lean_ctor_set(v___x_1386_, 2, v_options_1371_);
lean_ctor_set(v___x_1386_, 3, v_currRecDepth_1372_);
lean_ctor_set(v___x_1386_, 4, v_maxRecDepth_1373_);
lean_ctor_set(v___x_1386_, 5, v_ref_1385_);
lean_ctor_set(v___x_1386_, 6, v_currNamespace_1375_);
lean_ctor_set(v___x_1386_, 7, v_openDecls_1376_);
lean_ctor_set(v___x_1386_, 8, v_initHeartbeats_1377_);
lean_ctor_set(v___x_1386_, 9, v_maxHeartbeats_1378_);
lean_ctor_set(v___x_1386_, 10, v_quotContext_1379_);
lean_ctor_set(v___x_1386_, 11, v_currMacroScope_1380_);
lean_ctor_set(v___x_1386_, 12, v_cancelTk_x3f_1382_);
lean_ctor_set(v___x_1386_, 13, v_inheritedTraceOptions_1384_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*14, v_diag_1381_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*14 + 1, v_suppressElabErrors_1383_);
v___x_1387_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1365_, v___x_1386_, v___y_1367_);
lean_dec_ref_known(v___x_1386_, 14);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_ref_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1388_, v_msg_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v_ref_1388_);
return v_res_1393_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_1399_ = l_Lean_stringToMessageData(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(lean_object* v_attrName_1403_, lean_object* v_declName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1408_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_1409_ = l_Lean_MessageData_ofName(v_attrName_1403_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = 0;
v___x_1414_ = l_Lean_MessageData_ofConstName(v_declName_1404_, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1412_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1417_, v___y_1405_, v___y_1406_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_attrName_1419_, lean_object* v_declName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1419_, v_declName_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(uint8_t v___y_1425_, lean_object* v_as_1426_, size_t v_i_1427_, size_t v_stop_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_eq(v_i_1427_, v_stop_1428_);
if (v___x_1429_ == 0)
{
uint8_t v___x_1430_; uint8_t v___y_1432_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1430_ = 1;
v___x_1436_ = lean_array_uget_borrowed(v_as_1426_, v_i_1427_);
v___x_1437_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_1438_ = lean_name_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
v___y_1432_ = v___x_1429_;
goto v___jp_1431_;
}
else
{
if (v___x_1429_ == 0)
{
v___y_1432_ = v___y_1425_;
goto v___jp_1431_;
}
else
{
v___y_1432_ = v___x_1429_;
goto v___jp_1431_;
}
}
v___jp_1431_:
{
if (v___y_1432_ == 0)
{
size_t v___x_1433_; size_t v___x_1434_; 
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1427_, v___x_1433_);
v_i_1427_ = v___x_1434_;
goto _start;
}
else
{
return v___x_1430_;
}
}
}
else
{
uint8_t v___x_1439_; 
v___x_1439_ = 0;
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1440_, lean_object* v_as_1441_, lean_object* v_i_1442_, lean_object* v_stop_1443_){
_start:
{
uint8_t v___y_12769__boxed_1444_; size_t v_i_boxed_1445_; size_t v_stop_boxed_1446_; uint8_t v_res_1447_; lean_object* v_r_1448_; 
v___y_12769__boxed_1444_ = lean_unbox(v___y_1440_);
v_i_boxed_1445_ = lean_unbox_usize(v_i_1442_);
lean_dec(v_i_1442_);
v_stop_boxed_1446_ = lean_unbox_usize(v_stop_1443_);
lean_dec(v_stop_1443_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_12769__boxed_1444_, v_as_1441_, v_i_boxed_1445_, v_stop_boxed_1446_);
lean_dec_ref(v_as_1441_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1467_ = l_Lean_stringToMessageData(v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1470_ = l_Lean_stringToMessageData(v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v_name_1479_, lean_object* v_decl_1480_, lean_object* v_stx_1481_, uint8_t v_kind_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___f_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___x_1639_; uint8_t v___x_1640_; 
lean_inc(v_decl_1480_);
v___f_1565_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed), 6, 1);
lean_closure_set(v___f_1565_, 0, v_decl_1480_);
v___x_1639_ = 0;
v___x_1640_ = l_Lean_instBEqAttributeKind_beq(v_kind_1482_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v___f_1565_);
lean_dec(v_stx_1481_);
lean_dec(v_decl_1480_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v___x_1476_);
lean_dec(v___x_1474_);
v___x_1641_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1479_, v_kind_1482_, v___y_1483_, v___y_1484_);
return v___x_1641_;
}
else
{
goto v___jp_1634_;
}
v___jp_1486_:
{
lean_object* v___x_1489_; lean_object* v_env_1490_; lean_object* v_nextMacroScope_1491_; lean_object* v_ngen_1492_; lean_object* v_auxDeclNGen_1493_; lean_object* v_traceState_1494_; lean_object* v_messages_1495_; lean_object* v_infoState_1496_; lean_object* v_snapshotTasks_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1513_; 
v___x_1489_ = lean_st_ref_take(v___y_1488_);
v_env_1490_ = lean_ctor_get(v___x_1489_, 0);
v_nextMacroScope_1491_ = lean_ctor_get(v___x_1489_, 1);
v_ngen_1492_ = lean_ctor_get(v___x_1489_, 2);
v_auxDeclNGen_1493_ = lean_ctor_get(v___x_1489_, 3);
v_traceState_1494_ = lean_ctor_get(v___x_1489_, 4);
v_messages_1495_ = lean_ctor_get(v___x_1489_, 6);
v_infoState_1496_ = lean_ctor_get(v___x_1489_, 7);
v_snapshotTasks_1497_ = lean_ctor_get(v___x_1489_, 8);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1489_, 5);
lean_dec(v_unused_1514_);
v___x_1499_ = v___x_1489_;
v_isShared_1500_ = v_isSharedCheck_1513_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snapshotTasks_1497_);
lean_inc(v_infoState_1496_);
lean_inc(v_messages_1495_);
lean_inc(v_traceState_1494_);
lean_inc(v_auxDeclNGen_1493_);
lean_inc(v_ngen_1492_);
lean_inc(v_nextMacroScope_1491_);
lean_inc(v_env_1490_);
lean_dec(v___x_1489_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1513_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v_toEnvExtension_1502_; lean_object* v_asyncMode_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1501_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1502_ = lean_ctor_get(v___x_1501_, 0);
v_asyncMode_1503_ = lean_ctor_get(v_toEnvExtension_1502_, 2);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_decl_1480_);
lean_ctor_set(v___x_1504_, 1, v___y_1487_);
v___x_1505_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1501_, v_env_1490_, v___x_1504_, v_asyncMode_1503_, v___x_1474_);
v___x_1506_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 5, v___x_1506_);
lean_ctor_set(v___x_1499_, 0, v___x_1505_);
v___x_1508_ = v___x_1499_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_nextMacroScope_1491_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_ngen_1492_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_auxDeclNGen_1493_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_traceState_1494_);
lean_ctor_set(v_reuseFailAlloc_1512_, 5, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1512_, 6, v_messages_1495_);
lean_ctor_set(v_reuseFailAlloc_1512_, 7, v_infoState_1496_);
lean_ctor_set(v_reuseFailAlloc_1512_, 8, v_snapshotTasks_1497_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_st_ref_set(v___y_1488_, v___x_1508_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
}
v___jp_1515_:
{
lean_object* v___x_1519_; lean_object* v_env_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_st_ref_get(v___y_1518_);
v_env_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_ref(v_env_1520_);
lean_dec(v___x_1519_);
lean_inc(v___y_1516_);
v___x_1521_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1520_, v___y_1516_);
if (lean_obj_tag(v___x_1521_) == 1)
{
lean_object* v_val_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1524_ = l_Lean_MessageData_ofName(v___y_1516_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_MessageData_ofName(v_val_1522_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1523_);
v___x_1531_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1530_, v___y_1517_, v___y_1518_);
return v___x_1531_;
}
else
{
lean_dec(v___x_1521_);
v___y_1487_ = v___y_1516_;
v___y_1488_ = v___y_1518_;
goto v___jp_1486_;
}
}
v___jp_1532_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v___y_1534_);
v___x_1538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1539_ = l_Lean_MessageData_ofName(v_decl_1480_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
lean_inc_ref(v___y_1537_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___y_1537_);
v___x_1544_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_array_to_list(v___y_1536_);
v___x_1547_ = l_Lean_MessageData_andList(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1550_, v___y_1533_, v___y_1535_);
return v___x_1551_;
}
v___jp_1552_:
{
size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_sz_1558_ = lean_array_size(v___y_1554_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_1558_, v___x_1559_, v___y_1554_);
v___x_1561_ = lean_array_get_size(v___x_1560_);
v___x_1562_ = lean_nat_dec_lt(v___y_1553_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1533_ = v___y_1555_;
v___y_1534_ = v___y_1556_;
v___y_1535_ = v___y_1557_;
v___y_1536_ = v___x_1560_;
v___y_1537_ = v___x_1563_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1533_ = v___y_1555_;
v___y_1534_ = v___y_1556_;
v___y_1535_ = v___y_1557_;
v___y_1536_ = v___x_1560_;
v___y_1537_ = v___x_1564_;
goto v___jp_1532_;
}
}
v___jp_1566_:
{
lean_object* v___x_1572_; lean_object* v_env_1573_; lean_object* v___x_1574_; lean_object* v_ext_1575_; lean_object* v_toEnvExtension_1576_; lean_object* v_asyncMode_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_categories_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1572_ = lean_st_ref_get(v___y_1571_);
v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_env_1573_);
lean_dec(v___x_1572_);
v___x_1574_ = l_Lean_Parser_parserExtension;
v_ext_1575_ = lean_ctor_get(v___x_1574_, 1);
v_toEnvExtension_1576_ = lean_ctor_get(v_ext_1575_, 0);
v_asyncMode_1577_ = lean_ctor_get(v_toEnvExtension_1576_, 2);
v___x_1578_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1579_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1578_, v___x_1574_, v_env_1573_, v_asyncMode_1577_);
v_categories_1580_ = lean_ctor_get(v___x_1579_, 2);
lean_inc_ref(v_categories_1580_);
lean_dec(v___x_1579_);
v___x_1581_ = lean_mk_empty_array_with_capacity(v___x_1475_);
v___x_1582_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_categories_1580_, v___x_1581_, v___f_1565_, v___y_1570_, v___y_1571_);
lean_dec_ref(v_categories_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = lean_array_get_size(v_a_1583_);
v___x_1585_ = lean_nat_dec_eq(v___x_1584_, v___x_1475_);
if (v___x_1585_ == 0)
{
if (v___y_1569_ == 0)
{
lean_dec(v_a_1583_);
v___y_1516_ = v___y_1568_;
v___y_1517_ = v___y_1570_;
v___y_1518_ = v___y_1571_;
goto v___jp_1515_;
}
else
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_nat_dec_lt(v___x_1475_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec(v___x_1474_);
v___y_1553_ = v___y_1567_;
v___y_1554_ = v_a_1583_;
v___y_1555_ = v___y_1570_;
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1571_;
goto v___jp_1552_;
}
else
{
if (v___x_1586_ == 0)
{
lean_dec(v___x_1474_);
v___y_1553_ = v___y_1567_;
v___y_1554_ = v_a_1583_;
v___y_1555_ = v___y_1570_;
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1571_;
goto v___jp_1552_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1584_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_1569_, v_a_1583_, v___x_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_dec(v___x_1474_);
v___y_1553_ = v___y_1567_;
v___y_1554_ = v_a_1583_;
v___y_1555_ = v___y_1570_;
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1571_;
goto v___jp_1552_;
}
else
{
lean_dec(v_a_1583_);
v___y_1516_ = v___y_1568_;
v___y_1517_ = v___y_1570_;
v___y_1518_ = v___y_1571_;
goto v___jp_1515_;
}
}
}
}
}
else
{
lean_dec(v_a_1583_);
v___y_1516_ = v___y_1568_;
v___y_1517_ = v___y_1570_;
v___y_1518_ = v___y_1571_;
goto v___jp_1515_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v___y_1568_);
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
v_a_1590_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1582_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1582_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
v___jp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1602_ = l_Lean_Name_mkStr4(v___x_1476_, v___x_1477_, v___x_1601_, v___x_1478_);
lean_inc(v_stx_1481_);
v___x_1603_ = l_Lean_Syntax_isOfKind(v_stx_1481_, v___x_1602_);
lean_dec(v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v___f_1565_);
lean_dec(v_stx_1481_);
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
v___x_1604_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1605_ = l_Lean_MessageData_ofName(v_name_1479_);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1608_, v___y_1599_, v___y_1600_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_name_1479_);
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = l_Lean_Syntax_getArg(v_stx_1481_, v___x_1610_);
lean_dec(v_stx_1481_);
v___x_1612_ = lean_box(0);
lean_inc(v___x_1611_);
v___x_1613_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1611_, v___x_1612_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_n(v_a_1614_, 2);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = 0;
v___x_1616_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_a_1614_, v___x_1615_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; lean_object* v_env_1618_; uint8_t v___x_1619_; 
lean_dec_ref_known(v___x_1616_, 1);
v___x_1617_ = lean_st_ref_get(v___y_1600_);
v_env_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_env_1618_);
lean_dec(v___x_1617_);
v___x_1619_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1618_, v_a_1614_);
if (v___x_1619_ == 0)
{
if (v___x_1603_ == 0)
{
lean_dec(v___x_1611_);
v___y_1567_ = v___x_1610_;
v___y_1568_ = v_a_1614_;
v___y_1569_ = v___x_1603_;
v___y_1570_ = v___y_1599_;
v___y_1571_ = v___y_1600_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v___f_1565_);
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
v___x_1620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1621_ = l_Lean_MessageData_ofName(v_a_1614_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v___x_1611_, v___x_1624_, v___y_1599_, v___y_1600_);
lean_dec(v___x_1611_);
return v___x_1625_;
}
}
else
{
lean_dec(v___x_1611_);
v___y_1567_ = v___x_1610_;
v___y_1568_ = v_a_1614_;
v___y_1569_ = v___x_1603_;
v___y_1570_ = v___y_1599_;
v___y_1571_ = v___y_1600_;
goto v___jp_1566_;
}
}
else
{
lean_dec(v_a_1614_);
lean_dec(v___x_1611_);
lean_dec_ref(v___f_1565_);
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
return v___x_1616_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v___x_1611_);
lean_dec_ref(v___f_1565_);
lean_dec(v_decl_1480_);
lean_dec(v___x_1474_);
v_a_1626_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1613_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1613_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
v___jp_1634_:
{
lean_object* v___x_1635_; lean_object* v_env_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_st_ref_get(v___y_1484_);
v_env_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_ref(v_env_1636_);
lean_dec(v___x_1635_);
v___x_1637_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1636_, v_decl_1480_);
lean_dec_ref(v_env_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
v___y_1599_ = v___y_1483_;
v___y_1600_ = v___y_1484_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1637_, 1);
lean_dec_ref(v___f_1565_);
lean_dec(v_stx_1481_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v___x_1476_);
lean_dec(v___x_1474_);
v___x_1638_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_name_1479_, v_decl_1480_, v___y_1483_, v___y_1484_);
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v___x_1642_, lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v_name_1647_, lean_object* v_decl_1648_, lean_object* v_stx_1649_, lean_object* v_kind_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v_kind_boxed_1654_; lean_object* v_res_1655_; 
v_kind_boxed_1654_ = lean_unbox(v_kind_1650_);
v_res_1655_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v___x_1642_, v___x_1643_, v___x_1644_, v___x_1645_, v___x_1646_, v_name_1647_, v_decl_1648_, v_stx_1649_, v_kind_boxed_1654_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___x_1643_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1745_ = l_Lean_registerBuiltinAttribute(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1748_, lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1749_, v___y_1750_, v___y_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1754_, lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(v_00_u03b1_1754_, v_msg_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(lean_object* v_00_u03c3_1760_, lean_object* v_00_u03b2_1761_, lean_object* v_map_1762_, lean_object* v_init_1763_, lean_object* v_f_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_1762_, v_init_1763_, v_f_1764_, v___y_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03c3_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_map_1771_, lean_object* v_init_1772_, lean_object* v_f_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(v_00_u03c3_1769_, v_00_u03b2_1770_, v_map_1771_, v_init_1772_, v_f_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_map_1771_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1778_, lean_object* v_ref_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1779_, v_msg_1780_, v___y_1781_, v___y_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_ref_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(v_00_u03b1_1785_, v_ref_1786_, v_msg_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_ref_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1792_, lean_object* v_attrName_1793_, lean_object* v_declName_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1793_, v_declName_1794_, v___y_1795_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_attrName_1800_, lean_object* v_declName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(v_00_u03b1_1799_, v_attrName_1800_, v_declName_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(lean_object* v_00_u03b1_1806_, lean_object* v_name_1807_, uint8_t v_kind_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1807_, v_kind_1808_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___boxed(lean_object* v_00_u03b1_1813_, lean_object* v_name_1814_, lean_object* v_kind_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_kind_boxed_1819_; lean_object* v_res_1820_; 
v_kind_boxed_1819_ = lean_unbox(v_kind_1815_);
v_res_1820_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(v_00_u03b1_1813_, v_name_1814_, v_kind_boxed_1819_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1821_, lean_object* v_f_1822_, lean_object* v_init_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1822_, v_map_1821_, v_init_1823_, v___y_1824_, v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1828_, lean_object* v_f_1829_, lean_object* v_init_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1828_, v_f_1829_, v_init_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1835_, lean_object* v_00_u03c3_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_map_1838_, lean_object* v_f_1839_, lean_object* v_init_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1839_, v_map_1838_, v_init_1840_, v___y_1841_, v___y_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1845_, lean_object* v_00_u03c3_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_map_1848_, lean_object* v_f_1849_, lean_object* v_init_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1845_, v_00_u03c3_1846_, v_00_u03b2_1847_, v_map_1848_, v_f_1849_, v_init_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1856_, v_a_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_m_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(v_00_u03b2_1859_, v_m_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_m_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1863_, lean_object* v_00_u03c3_1864_, lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_f_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1867_, v_x_1868_, v_x_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1874_, lean_object* v_00_u03c3_1875_, lean_object* v_00_u03b1_1876_, lean_object* v_00_u03b2_1877_, lean_object* v_f_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03c3_1874_, v_00_u03c3_1875_, v_00_u03b1_1876_, v_00_u03b2_1877_, v_f_1878_, v_x_1879_, v_x_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
uint8_t v_res_1892_; lean_object* v_r_1893_; 
v_res_1892_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_00_u03b2_1889_, v_x_1890_, v_x_1891_);
lean_dec_ref(v_x_1891_);
lean_dec_ref(v_x_1890_);
v_r_1893_ = lean_box(v_res_1892_);
return v_r_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1894_, lean_object* v_a_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1898_, lean_object* v_a_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(v_00_u03b2_1898_, v_a_1899_, v_x_1900_);
lean_dec(v_x_1900_);
lean_dec(v_a_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(lean_object* v_00_u03b1_1902_, lean_object* v_00_u03b2_1903_, lean_object* v_00_u03c3_1904_, lean_object* v_00_u03c3_1905_, lean_object* v_f_1906_, lean_object* v_as_1907_, size_t v_i_1908_, size_t v_stop_1909_, lean_object* v_b_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_1906_, v_as_1907_, v_i_1908_, v_stop_1909_, v_b_1910_, v___y_1911_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_00_u03c3_1917_, lean_object* v_00_u03c3_1918_, lean_object* v_f_1919_, lean_object* v_as_1920_, lean_object* v_i_1921_, lean_object* v_stop_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1922_);
lean_dec(v_stop_1922_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(v_00_u03b1_1915_, v_00_u03b2_1916_, v_00_u03c3_1917_, v_00_u03c3_1918_, v_f_1919_, v_as_1920_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v_as_1920_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(lean_object* v_00_u03c3_1930_, lean_object* v_00_u03c3_1931_, lean_object* v_00_u03b1_1932_, lean_object* v_00_u03b2_1933_, lean_object* v_f_1934_, lean_object* v_keys_1935_, lean_object* v_vals_1936_, lean_object* v_heq_1937_, lean_object* v_i_1938_, lean_object* v_acc_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_1934_, v_keys_1935_, v_vals_1936_, v_i_1938_, v_acc_1939_, v___y_1940_, v___y_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03c3_1944_, lean_object* v_00_u03c3_1945_, lean_object* v_00_u03b1_1946_, lean_object* v_00_u03b2_1947_, lean_object* v_f_1948_, lean_object* v_keys_1949_, lean_object* v_vals_1950_, lean_object* v_heq_1951_, lean_object* v_i_1952_, lean_object* v_acc_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(v_00_u03c3_1944_, v_00_u03c3_1945_, v_00_u03b1_1946_, v_00_u03b2_1947_, v_f_1948_, v_keys_1949_, v_vals_1950_, v_heq_1951_, v_i_1952_, v_acc_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_vals_1950_);
lean_dec_ref(v_keys_1949_);
return v_res_1957_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1958_, lean_object* v_x_1959_, size_t v_x_1960_, lean_object* v_x_1961_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1959_, v_x_1960_, v_x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
size_t v_x_13591__boxed_1967_; uint8_t v_res_1968_; lean_object* v_r_1969_; 
v_x_13591__boxed_1967_ = lean_unbox_usize(v_x_1965_);
lean_dec(v_x_1965_);
v_res_1968_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(v_00_u03b2_1963_, v_x_1964_, v_x_13591__boxed_1967_, v_x_1966_);
lean_dec_ref(v_x_1966_);
lean_dec_ref(v_x_1964_);
v_r_1969_ = lean_box(v_res_1968_);
return v_r_1969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(lean_object* v_00_u03b2_1970_, lean_object* v_keys_1971_, lean_object* v_vals_1972_, lean_object* v_heq_1973_, lean_object* v_i_1974_, lean_object* v_k_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1971_, v_i_1974_, v_k_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v_00_u03b2_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_heq_1980_, lean_object* v_i_1981_, lean_object* v_k_1982_){
_start:
{
uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_res_1983_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(v_00_u03b2_1977_, v_keys_1978_, v_vals_1979_, v_heq_1980_, v_i_1981_, v_k_1982_);
lean_dec_ref(v_k_1982_);
lean_dec_ref(v_vals_1979_);
lean_dec_ref(v_keys_1978_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1985_, lean_object* v_x_1986_){
_start:
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1989_; 
v_fst_1987_ = lean_ctor_get(v_x_1986_, 0);
lean_inc(v_fst_1987_);
v_snd_1988_ = lean_ctor_get(v_x_1986_, 1);
lean_inc(v_snd_1988_);
lean_dec_ref(v_x_1986_);
v___x_1989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1987_, v_snd_1988_, v_as_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1990_, lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v_l_1994_; lean_object* v_r_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_k_1992_ = lean_ctor_get(v_x_1991_, 1);
v_v_1993_ = lean_ctor_get(v_x_1991_, 2);
v_l_1994_ = lean_ctor_get(v_x_1991_, 3);
v_r_1995_ = lean_ctor_get(v_x_1991_, 4);
v___x_1996_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1990_, v_l_1994_);
lean_inc(v_v_1993_);
lean_inc(v_k_1992_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_k_1992_);
lean_ctor_set(v___x_1997_, 1, v_v_1993_);
v___x_1998_ = lean_array_push(v___x_1996_, v___x_1997_);
v_init_1990_ = v___x_1998_;
v_x_1991_ = v_r_1995_;
goto _start;
}
else
{
return v_init_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2000_, v_x_2001_);
lean_dec(v_x_2001_);
return v_res_2002_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_2003_, lean_object* v_x2_2004_){
_start:
{
lean_object* v_fst_2005_; lean_object* v_fst_2006_; uint8_t v___x_2007_; 
v_fst_2005_ = lean_ctor_get(v_x1_2003_, 0);
v_fst_2006_ = lean_ctor_get(v_x2_2004_, 0);
v___x_2007_ = l_Lean_Name_quickLt(v_fst_2005_, v_fst_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_2008_, lean_object* v_x2_2009_){
_start:
{
uint8_t v_res_2010_; lean_object* v_r_2011_; 
v_res_2010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_2008_, v_x2_2009_);
lean_dec_ref(v_x2_2009_);
lean_dec_ref(v_x1_2008_);
v_r_2011_ = lean_box(v_res_2010_);
return v_r_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_2012_, lean_object* v_pivot_2013_, lean_object* v_as_2014_, lean_object* v_i_2015_, lean_object* v_k_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_nat_dec_lt(v_k_2016_, v_hi_2012_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_k_2016_);
v___x_2018_ = lean_array_fswap(v_as_2014_, v_i_2015_, v_hi_2012_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_i_2015_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v_fst_2021_; lean_object* v_fst_2022_; uint8_t v___x_2023_; 
v___x_2020_ = lean_array_fget_borrowed(v_as_2014_, v_k_2016_);
v_fst_2021_ = lean_ctor_get(v___x_2020_, 0);
v_fst_2022_ = lean_ctor_get(v_pivot_2013_, 0);
v___x_2023_ = l_Lean_Name_quickLt(v_fst_2021_, v_fst_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_k_2016_, v___x_2024_);
lean_dec(v_k_2016_);
v_k_2016_ = v___x_2025_;
goto _start;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = lean_array_fswap(v_as_2014_, v_i_2015_, v_k_2016_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_i_2015_, v___x_2028_);
lean_dec(v_i_2015_);
v___x_2030_ = lean_nat_add(v_k_2016_, v___x_2028_);
lean_dec(v_k_2016_);
v_as_2014_ = v___x_2027_;
v_i_2015_ = v___x_2029_;
v_k_2016_ = v___x_2030_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_2032_, lean_object* v_pivot_2033_, lean_object* v_as_2034_, lean_object* v_i_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2032_, v_pivot_2033_, v_as_2034_, v_i_2035_, v_k_2036_);
lean_dec_ref(v_pivot_2033_);
lean_dec(v_hi_2032_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_2038_, lean_object* v_as_2039_, lean_object* v_lo_2040_, lean_object* v_hi_2041_){
_start:
{
lean_object* v___y_2043_; uint8_t v___x_2053_; 
v___x_2053_ = lean_nat_dec_lt(v_lo_2040_, v_hi_2041_);
if (v___x_2053_ == 0)
{
lean_dec(v_lo_2040_);
return v_as_2039_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v_mid_2056_; lean_object* v___y_2058_; lean_object* v___y_2064_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2054_ = lean_nat_add(v_lo_2040_, v_hi_2041_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v_mid_2056_ = lean_nat_shiftr(v___x_2054_, v___x_2055_);
lean_dec(v___x_2054_);
v___x_2069_ = lean_array_fget_borrowed(v_as_2039_, v_mid_2056_);
v___x_2070_ = lean_array_fget_borrowed(v_as_2039_, v_lo_2040_);
v___x_2071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
v___y_2064_ = v_as_2039_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_array_fswap(v_as_2039_, v_lo_2040_, v_mid_2056_);
v___y_2064_ = v___x_2072_;
goto v___jp_2063_;
}
v___jp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_array_fget_borrowed(v___y_2058_, v_mid_2056_);
v___x_2060_ = lean_array_fget_borrowed(v___y_2058_, v_hi_2041_);
v___x_2061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec(v_mid_2056_);
v___y_2043_ = v___y_2058_;
goto v___jp_2042_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_array_fswap(v___y_2058_, v_mid_2056_, v_hi_2041_);
lean_dec(v_mid_2056_);
v___y_2043_ = v___x_2062_;
goto v___jp_2042_;
}
}
v___jp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = lean_array_fget_borrowed(v___y_2064_, v_hi_2041_);
v___x_2066_ = lean_array_fget_borrowed(v___y_2064_, v_lo_2040_);
v___x_2067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
v___y_2058_ = v___y_2064_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_array_fswap(v___y_2064_, v_lo_2040_, v_hi_2041_);
v___y_2058_ = v___x_2068_;
goto v___jp_2057_;
}
}
}
v___jp_2042_:
{
lean_object* v_pivot_2044_; lean_object* v___x_2045_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; uint8_t v___x_2048_; 
v_pivot_2044_ = lean_array_fget(v___y_2043_, v_hi_2041_);
lean_inc_n(v_lo_2040_, 2);
v___x_2045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2041_, v_pivot_2044_, v___y_2043_, v_lo_2040_, v_lo_2040_);
lean_dec(v_pivot_2044_);
v_fst_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v___x_2045_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2045_);
v___x_2048_ = lean_nat_dec_le(v_hi_2041_, v_fst_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2038_, v_snd_2047_, v_lo_2040_, v_fst_2046_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_add(v_fst_2046_, v___x_2050_);
lean_dec(v_fst_2046_);
v_as_2039_ = v___x_2049_;
v_lo_2040_ = v___x_2051_;
goto _start;
}
else
{
lean_dec(v_fst_2046_);
lean_dec(v_lo_2040_);
return v_snd_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_2073_, lean_object* v_as_2074_, lean_object* v_lo_2075_, lean_object* v_hi_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2073_, v_as_2074_, v_lo_2075_, v_hi_2076_);
lean_dec(v_hi_2076_);
lean_dec(v_n_2073_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_2080_, lean_object* v_s_2081_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___y_2087_; lean_object* v___y_2088_; uint8_t v___x_2091_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2084_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2083_, v_s_2081_);
v___x_2085_ = lean_array_get_size(v___x_2084_);
v___x_2091_ = lean_nat_dec_eq(v___x_2085_, v___x_2082_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___y_2095_; uint8_t v___x_2097_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_nat_sub(v___x_2085_, v___x_2092_);
v___x_2097_ = lean_nat_dec_le(v___x_2082_, v___x_2093_);
if (v___x_2097_ == 0)
{
lean_inc(v___x_2093_);
v___y_2095_ = v___x_2093_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___x_2082_;
goto v___jp_2094_;
}
v___jp_2094_:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_le(v___y_2095_, v___x_2093_);
if (v___x_2096_ == 0)
{
lean_dec(v___x_2093_);
lean_inc(v___y_2095_);
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2095_;
goto v___jp_2086_;
}
else
{
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___x_2093_;
goto v___jp_2086_;
}
}
}
else
{
lean_object* v___x_2098_; 
lean_inc_ref_n(v___x_2084_, 2);
v___x_2098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2084_);
lean_ctor_set(v___x_2098_, 1, v___x_2084_);
lean_ctor_set(v___x_2098_, 2, v___x_2084_);
return v___x_2098_;
}
v___jp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2085_, v___x_2084_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_inc_ref_n(v___x_2089_, 2);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_2099_, lean_object* v_s_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_2099_, v_s_2100_);
lean_dec(v_s_2100_);
lean_dec_ref(v_x_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2105_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2104_, v_es_2102_);
v___x_2106_ = lean_array_get_size(v___x_2105_);
v___x_2107_ = lean_nat_dec_eq(v___x_2106_, v___x_2103_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___y_2111_; uint8_t v___x_2115_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_sub(v___x_2106_, v___x_2108_);
v___x_2115_ = lean_nat_dec_le(v___x_2103_, v___x_2109_);
if (v___x_2115_ == 0)
{
lean_inc(v___x_2109_);
v___y_2111_ = v___x_2109_;
goto v___jp_2110_;
}
else
{
v___y_2111_ = v___x_2103_;
goto v___jp_2110_;
}
v___jp_2110_:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_le(v___y_2111_, v___x_2109_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_dec(v___x_2109_);
lean_inc(v___y_2111_);
v___x_2113_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2106_, v___x_2105_, v___y_2111_, v___y_2111_);
lean_dec(v___y_2111_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2106_, v___x_2105_, v___y_2111_, v___x_2109_);
lean_dec(v___x_2109_);
return v___x_2114_;
}
}
}
else
{
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_2116_);
lean_dec(v_es_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_2118_, lean_object* v_x_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2118_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_2123_, lean_object* v_x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_2123_, v_x_2124_, v___y_2125_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_x_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2154_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_2157_, lean_object* v_t_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2157_, v_t_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2160_, lean_object* v_t_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_2160_, v_t_2161_);
lean_dec(v_t_2161_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_2163_, lean_object* v_as_2164_, lean_object* v_lo_2165_, lean_object* v_hi_2166_, lean_object* v_w_2167_, lean_object* v_hlo_2168_, lean_object* v_hhi_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2163_, v_as_2164_, v_lo_2165_, v_hi_2166_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_2171_, lean_object* v_as_2172_, lean_object* v_lo_2173_, lean_object* v_hi_2174_, lean_object* v_w_2175_, lean_object* v_hlo_2176_, lean_object* v_hhi_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_2171_, v_as_2172_, v_lo_2173_, v_hi_2174_, v_w_2175_, v_hlo_2176_, v_hhi_2177_);
lean_dec(v_hi_2174_);
lean_dec(v_n_2171_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_2179_, lean_object* v_lo_2180_, lean_object* v_hi_2181_, lean_object* v_hhi_2182_, lean_object* v_pivot_2183_, lean_object* v_as_2184_, lean_object* v_i_2185_, lean_object* v_k_2186_, lean_object* v_ilo_2187_, lean_object* v_ik_2188_, lean_object* v_w_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2181_, v_pivot_2183_, v_as_2184_, v_i_2185_, v_k_2186_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_2191_, lean_object* v_lo_2192_, lean_object* v_hi_2193_, lean_object* v_hhi_2194_, lean_object* v_pivot_2195_, lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_k_2198_, lean_object* v_ilo_2199_, lean_object* v_ik_2200_, lean_object* v_w_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(v_n_2191_, v_lo_2192_, v_hi_2193_, v_hhi_2194_, v_pivot_2195_, v_as_2196_, v_i_2197_, v_k_2198_, v_ilo_2199_, v_ik_2200_, v_w_2201_);
lean_dec_ref(v_pivot_2195_);
lean_dec(v_hi_2193_);
lean_dec(v_lo_2192_);
lean_dec(v_n_2191_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_2207_, lean_object* v___x_2208_, lean_object* v_toPure_2209_, lean_object* v___f_2210_, lean_object* v_env_2211_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2211_, v_tag_2207_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; lean_object* v_toEnvExtension_2217_; lean_object* v_asyncMode_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v___f_2210_);
v___x_2216_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2217_ = lean_ctor_get(v___x_2216_, 0);
v_asyncMode_2218_ = lean_ctor_get(v_toEnvExtension_2217_, 2);
v___x_2219_ = lean_box(0);
v___x_2220_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2208_, v___x_2216_, v_env_2211_, v_asyncMode_2218_, v___x_2219_);
v___x_2221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2220_, v_tag_2207_);
lean_dec(v_tag_2207_);
lean_dec(v___x_2220_);
v___x_2222_ = lean_apply_2(v_toPure_2209_, lean_box(0), v___x_2221_);
return v___x_2222_;
}
else
{
lean_object* v_val_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_val_2223_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2224_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2225_ = 0;
v___x_2226_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2208_, v___x_2224_, v_env_2211_, v_val_2223_, v___x_2225_);
lean_dec(v_val_2223_);
lean_dec_ref(v_env_2211_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_array_get_size(v___x_2226_);
v___x_2229_ = lean_nat_dec_lt(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_dec_ref(v___x_2226_);
lean_dec_ref(v___f_2210_);
lean_dec(v_tag_2207_);
goto v___jp_2212_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_nat_sub(v___x_2228_, v___x_2230_);
v___x_2232_ = lean_nat_dec_le(v___x_2227_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_dec(v___x_2231_);
lean_dec_ref(v___x_2226_);
lean_dec_ref(v___f_2210_);
lean_dec(v_tag_2207_);
goto v___jp_2212_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_tag_2207_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_2236_ = l_Array_binSearchAux___redArg(v___f_2210_, v___x_2235_, v___x_2226_, v___x_2234_, v___x_2227_, v___x_2231_);
lean_dec_ref(v___x_2226_);
if (lean_obj_tag(v___x_2236_) == 0)
{
goto v___jp_2212_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_val_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_snd_2241_; lean_object* v___x_2243_; 
v_snd_2241_ = lean_ctor_get(v_val_2237_, 1);
lean_inc(v_snd_2241_);
lean_dec(v_val_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_snd_2241_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_apply_2(v_toPure_2209_, lean_box(0), v___x_2243_);
return v___x_2244_;
}
}
}
}
}
}
v___jp_2212_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_apply_2(v_toPure_2209_, lean_box(0), v___x_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_tag_2250_){
_start:
{
lean_object* v_toApplicative_2251_; lean_object* v_toBind_2252_; lean_object* v_getEnv_2253_; lean_object* v_toPure_2254_; lean_object* v___f_2255_; lean_object* v___x_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; 
v_toApplicative_2251_ = lean_ctor_get(v_inst_2248_, 0);
lean_inc_ref(v_toApplicative_2251_);
v_toBind_2252_ = lean_ctor_get(v_inst_2248_, 1);
lean_inc(v_toBind_2252_);
lean_dec_ref(v_inst_2248_);
v_getEnv_2253_ = lean_ctor_get(v_inst_2249_, 0);
lean_inc(v_getEnv_2253_);
lean_dec_ref(v_inst_2249_);
v_toPure_2254_ = lean_ctor_get(v_toApplicative_2251_, 1);
lean_inc(v_toPure_2254_);
lean_dec_ref(v_toApplicative_2251_);
v___f_2255_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0));
v___x_2256_ = lean_box(1);
v___f_2257_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2257_, 0, v_tag_2250_);
lean_closure_set(v___f_2257_, 1, v___x_2256_);
lean_closure_set(v___f_2257_, 2, v_toPure_2254_);
lean_closure_set(v___f_2257_, 3, v___f_2255_);
v___x_2258_ = lean_apply_4(v_toBind_2252_, lean_box(0), lean_box(0), v_getEnv_2253_, v___f_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_tag_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_2260_, v_inst_2261_, v_tag_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_2264_, lean_object* v_k_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_array_push(v_l_2264_, v_k_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_2268_, lean_object* v_x2_2269_){
_start:
{
uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2270_ = 1;
v___x_2271_ = l_Lean_Name_toString(v_x1_2268_, v___x_2270_);
v___x_2272_ = l_Lean_Name_toString(v_x2_2269_, v___x_2270_);
v___x_2273_ = lean_string_dec_lt(v___x_2271_, v___x_2272_);
lean_dec_ref(v___x_2272_);
lean_dec_ref(v___x_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_2274_, lean_object* v_x2_2275_){
_start:
{
uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_res_2276_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_2274_, v_x2_2275_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_2278_, lean_object* v_a_2279_, lean_object* v_b_2280_, lean_object* v_c_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = l_Lean_NameSet_insert(v_c_2281_, v_a_2279_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
v___x_2284_ = lean_apply_2(v_toPure_2278_, lean_box(0), v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_2285_, lean_object* v_a_2286_, lean_object* v_b_2287_, lean_object* v_c_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_2285_, v_a_2286_, v_b_2287_, v_c_2288_);
lean_dec_ref(v_b_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_2290_, lean_object* v_a_2291_, lean_object* v_x_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_fst_2294_; lean_object* v_found_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_fst_2294_ = lean_ctor_get(v_a_2291_, 0);
lean_inc(v_fst_2294_);
lean_dec_ref(v_a_2291_);
v_found_2295_ = l_Lean_NameSet_insert(v___y_2293_, v_fst_2294_);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_found_2295_);
v___x_2297_ = lean_apply_2(v_toPure_2290_, lean_box(0), v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_2298_, lean_object* v___f_2299_, lean_object* v_toBind_2300_, lean_object* v___f_2301_, lean_object* v_a_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
size_t v_sz_2305_; size_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_sz_2305_ = lean_array_size(v_a_2302_);
v___x_2306_ = ((size_t)0ULL);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2298_, v_a_2302_, v___f_2299_, v_sz_2305_, v___x_2306_, v___y_2304_);
v___x_2308_ = lean_apply_4(v_toBind_2300_, lean_box(0), lean_box(0), v___x_2307_, v___f_2301_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_2309_, lean_object* v___f_2310_, lean_object* v___f_2311_, lean_object* v_____s_2312_){
_start:
{
lean_object* v___y_2314_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2330_; 
if (lean_obj_tag(v_____s_2312_) == 0)
{
lean_object* v_size_2339_; 
v_size_2339_ = lean_ctor_get(v_____s_2312_, 0);
lean_inc(v_size_2339_);
v___y_2330_ = v_size_2339_;
goto v___jp_2329_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
v___y_2330_ = v___x_2340_;
goto v___jp_2329_;
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_array_to_list(v___y_2314_);
v___x_2316_ = lean_apply_2(v_toPure_2309_, lean_box(0), v___x_2315_);
return v___x_2316_;
}
v___jp_2317_:
{
lean_object* v___x_2322_; 
v___x_2322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2310_, v___y_2319_, v___y_2318_, v___y_2320_, v___y_2321_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2321_);
lean_dec(v___y_2319_);
v___y_2314_ = v___x_2322_;
goto v___jp_2313_;
}
v___jp_2323_:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_nat_dec_le(v___y_2327_, v___y_2326_);
if (v___x_2328_ == 0)
{
lean_dec(v___y_2326_);
lean_inc(v___y_2327_);
v___y_2318_ = v___y_2324_;
v___y_2319_ = v___y_2325_;
v___y_2320_ = v___y_2327_;
v___y_2321_ = v___y_2327_;
goto v___jp_2317_;
}
else
{
v___y_2318_ = v___y_2324_;
v___y_2319_ = v___y_2325_;
v___y_2320_ = v___y_2327_;
v___y_2321_ = v___y_2326_;
goto v___jp_2317_;
}
}
v___jp_2329_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2331_ = lean_mk_empty_array_with_capacity(v___y_2330_);
lean_dec(v___y_2330_);
v___x_2332_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2311_, v___x_2331_, v_____s_2312_);
v___x_2333_ = lean_array_get_size(v___x_2332_);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_nat_dec_eq(v___x_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_sub(v___x_2333_, v___x_2336_);
v___x_2338_ = lean_nat_dec_le(v___x_2334_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_inc(v___x_2337_);
v___y_2324_ = v___x_2332_;
v___y_2325_ = v___x_2333_;
v___y_2326_ = v___x_2337_;
v___y_2327_ = v___x_2337_;
goto v___jp_2323_;
}
else
{
v___y_2324_ = v___x_2332_;
v___y_2325_ = v___x_2333_;
v___y_2326_ = v___x_2337_;
v___y_2327_ = v___x_2334_;
goto v___jp_2323_;
}
}
else
{
lean_dec_ref(v___f_2310_);
v___y_2314_ = v___x_2332_;
goto v___jp_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2341_, lean_object* v_toEnvExtension_2342_, lean_object* v_env_2343_, lean_object* v_asyncMode_2344_, lean_object* v___x_2345_, lean_object* v_inst_2346_, lean_object* v___f_2347_, lean_object* v_toBind_2348_, lean_object* v___f_2349_, lean_object* v_____s_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v_importedEntries_2352_; size_t v_sz_2353_; size_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2341_, v_toEnvExtension_2342_, v_env_2343_, v_asyncMode_2344_, v___x_2345_);
v_importedEntries_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc_ref(v_importedEntries_2352_);
lean_dec(v___x_2351_);
v_sz_2353_ = lean_array_size(v_importedEntries_2352_);
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2346_, v_importedEntries_2352_, v___f_2347_, v_sz_2353_, v___x_2354_, v_____s_2350_);
v___x_2356_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2355_, v___f_2349_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2357_, lean_object* v_toEnvExtension_2358_, lean_object* v_env_2359_, lean_object* v_asyncMode_2360_, lean_object* v___x_2361_, lean_object* v_inst_2362_, lean_object* v___f_2363_, lean_object* v_toBind_2364_, lean_object* v___f_2365_, lean_object* v_____s_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2357_, v_toEnvExtension_2358_, v_env_2359_, v_asyncMode_2360_, v___x_2361_, v_inst_2362_, v___f_2363_, v_toBind_2364_, v___f_2365_, v_____s_2366_);
lean_dec(v_asyncMode_2360_);
lean_dec_ref(v_toEnvExtension_2358_);
lean_dec_ref(v___x_2357_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2368_, lean_object* v_inst_2369_, lean_object* v___f_2370_, lean_object* v_toBind_2371_, lean_object* v___f_2372_, lean_object* v___x_2373_, lean_object* v___f_2374_, lean_object* v___f_2375_, lean_object* v_env_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v_toEnvExtension_2378_; lean_object* v_asyncMode_2379_; lean_object* v_found_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2377_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2378_ = lean_ctor_get(v___x_2377_, 0);
v_asyncMode_2379_ = lean_ctor_get(v_toEnvExtension_2378_, 2);
v_found_2380_ = l_Lean_NameSet_empty;
v___x_2381_ = lean_box(0);
lean_inc_n(v_toBind_2371_, 2);
lean_inc_ref(v_inst_2369_);
lean_inc(v_asyncMode_2379_);
lean_inc_ref(v_env_2376_);
lean_inc_ref(v_toEnvExtension_2378_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2382_, 0, v___x_2368_);
lean_closure_set(v___f_2382_, 1, v_toEnvExtension_2378_);
lean_closure_set(v___f_2382_, 2, v_env_2376_);
lean_closure_set(v___f_2382_, 3, v_asyncMode_2379_);
lean_closure_set(v___f_2382_, 4, v___x_2381_);
lean_closure_set(v___f_2382_, 5, v_inst_2369_);
lean_closure_set(v___f_2382_, 6, v___f_2370_);
lean_closure_set(v___f_2382_, 7, v_toBind_2371_);
lean_closure_set(v___f_2382_, 8, v___f_2372_);
v___x_2383_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2373_, v___x_2377_, v_env_2376_, v_asyncMode_2379_, v___x_2381_);
v___x_2384_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2369_, v___f_2374_, v_found_2380_, v___x_2383_);
v___x_2385_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2384_, v___f_2375_);
v___x_2386_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2385_, v___f_2382_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_box(1);
v___x_2390_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2391_, lean_object* v_inst_2392_){
_start:
{
lean_object* v_toApplicative_2393_; lean_object* v_toBind_2394_; lean_object* v_getEnv_2395_; lean_object* v_toPure_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___f_2402_; lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; 
v_toApplicative_2393_ = lean_ctor_get(v_inst_2391_, 0);
v_toBind_2394_ = lean_ctor_get(v_inst_2391_, 1);
lean_inc_n(v_toBind_2394_, 3);
v_getEnv_2395_ = lean_ctor_get(v_inst_2392_, 0);
lean_inc(v_getEnv_2395_);
lean_dec_ref(v_inst_2392_);
v_toPure_2396_ = lean_ctor_get(v_toApplicative_2393_, 1);
v___f_2397_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2398_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2399_ = lean_box(1);
v___x_2400_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2396_, 5);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2401_, 0, v_toPure_2396_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2402_, 0, v_toPure_2396_);
v___f_2403_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2403_, 0, v_toPure_2396_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2404_, 0, v_toPure_2396_);
lean_inc_ref(v_inst_2391_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2405_, 0, v_inst_2391_);
lean_closure_set(v___f_2405_, 1, v___f_2403_);
lean_closure_set(v___f_2405_, 2, v_toBind_2394_);
lean_closure_set(v___f_2405_, 3, v___f_2404_);
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2406_, 0, v_toPure_2396_);
lean_closure_set(v___f_2406_, 1, v___f_2398_);
lean_closure_set(v___f_2406_, 2, v___f_2397_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2407_, 0, v___x_2400_);
lean_closure_set(v___f_2407_, 1, v_inst_2391_);
lean_closure_set(v___f_2407_, 2, v___f_2405_);
lean_closure_set(v___f_2407_, 3, v_toBind_2394_);
lean_closure_set(v___f_2407_, 4, v___f_2406_);
lean_closure_set(v___f_2407_, 5, v___x_2399_);
lean_closure_set(v___f_2407_, 6, v___f_2402_);
lean_closure_set(v___f_2407_, 7, v___f_2401_);
v___x_2408_ = lean_apply_4(v_toBind_2394_, lean_box(0), lean_box(0), v_getEnv_2395_, v___f_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2410_, v_inst_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2413_, lean_object* v_k_2414_, lean_object* v_v_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v_k_2414_);
lean_ctor_set(v___x_2416_, 1, v_v_2415_);
v___x_2417_ = lean_array_push(v_arr_2413_, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2418_, lean_object* v_x2_2419_){
_start:
{
lean_object* v_fst_2420_; lean_object* v_fst_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v_fst_2420_ = lean_ctor_get(v_x1_2418_, 0);
lean_inc(v_fst_2420_);
lean_dec_ref(v_x1_2418_);
v_fst_2421_ = lean_ctor_get(v_x2_2419_, 0);
lean_inc(v_fst_2421_);
lean_dec_ref(v_x2_2419_);
v___x_2422_ = 1;
v___x_2423_ = l_Lean_Name_toString(v_fst_2420_, v___x_2422_);
v___x_2424_ = l_Lean_Name_toString(v_fst_2421_, v___x_2422_);
v___x_2425_ = lean_string_dec_lt(v___x_2423_, v___x_2424_);
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2426_, lean_object* v_x2_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2426_, v_x2_2427_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v_c_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2431_, v_b_2432_, v_c_2433_);
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
v___x_2436_ = lean_apply_2(v_toPure_2430_, lean_box(0), v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_fst_2441_; lean_object* v_snd_2442_; lean_object* v_found_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_fst_2441_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_fst_2441_);
v_snd_2442_ = lean_ctor_get(v_a_2438_, 1);
lean_inc(v_snd_2442_);
lean_dec_ref(v_a_2438_);
v_found_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2441_, v_snd_2442_, v___y_2440_);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_found_2443_);
v___x_2445_ = lean_apply_2(v_toPure_2437_, lean_box(0), v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2446_, lean_object* v___f_2447_, lean_object* v___f_2448_, lean_object* v_____s_2449_){
_start:
{
lean_object* v___y_2451_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_arr_2456_; lean_object* v___x_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; uint8_t v___x_2462_; 
v___x_2454_ = lean_unsigned_to_nat(0u);
v___x_2455_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2456_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2447_, v___x_2455_, v_____s_2449_);
v___x_2457_ = lean_array_get_size(v_arr_2456_);
v___x_2462_ = lean_nat_dec_eq(v___x_2457_, v___x_2454_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___y_2466_; uint8_t v___x_2468_; 
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_sub(v___x_2457_, v___x_2463_);
v___x_2468_ = lean_nat_dec_le(v___x_2454_, v___x_2464_);
if (v___x_2468_ == 0)
{
lean_inc(v___x_2464_);
v___y_2466_ = v___x_2464_;
goto v___jp_2465_;
}
else
{
v___y_2466_ = v___x_2454_;
goto v___jp_2465_;
}
v___jp_2465_:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_nat_dec_le(v___y_2466_, v___x_2464_);
if (v___x_2467_ == 0)
{
lean_dec(v___x_2464_);
lean_inc(v___y_2466_);
v___y_2459_ = v___y_2466_;
v___y_2460_ = v___y_2466_;
goto v___jp_2458_;
}
else
{
v___y_2459_ = v___y_2466_;
v___y_2460_ = v___x_2464_;
goto v___jp_2458_;
}
}
}
else
{
lean_dec_ref(v___f_2448_);
v___y_2451_ = v_arr_2456_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_array_to_list(v___y_2451_);
v___x_2453_ = lean_apply_2(v_toPure_2446_, lean_box(0), v___x_2452_);
return v___x_2453_;
}
v___jp_2458_:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2448_, v___x_2457_, v_arr_2456_, v___y_2459_, v___y_2460_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2460_);
v___y_2451_ = v___x_2461_;
goto v___jp_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2469_, lean_object* v_inst_2470_, lean_object* v___f_2471_, lean_object* v_toBind_2472_, lean_object* v___f_2473_, lean_object* v___x_2474_, lean_object* v___f_2475_, lean_object* v___f_2476_, lean_object* v_env_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v_toEnvExtension_2479_; lean_object* v_asyncMode_2480_; lean_object* v_found_2481_; lean_object* v___x_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2478_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2479_ = lean_ctor_get(v___x_2478_, 0);
v_asyncMode_2480_ = lean_ctor_get(v_toEnvExtension_2479_, 2);
v_found_2481_ = lean_box(1);
v___x_2482_ = lean_box(0);
lean_inc_n(v_toBind_2472_, 2);
lean_inc_ref(v_inst_2470_);
lean_inc(v_asyncMode_2480_);
lean_inc_ref(v_env_2477_);
lean_inc_ref(v_toEnvExtension_2479_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2483_, 0, v___x_2469_);
lean_closure_set(v___f_2483_, 1, v_toEnvExtension_2479_);
lean_closure_set(v___f_2483_, 2, v_env_2477_);
lean_closure_set(v___f_2483_, 3, v_asyncMode_2480_);
lean_closure_set(v___f_2483_, 4, v___x_2482_);
lean_closure_set(v___f_2483_, 5, v_inst_2470_);
lean_closure_set(v___f_2483_, 6, v___f_2471_);
lean_closure_set(v___f_2483_, 7, v_toBind_2472_);
lean_closure_set(v___f_2483_, 8, v___f_2473_);
v___x_2484_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2474_, v___x_2478_, v_env_2477_, v_asyncMode_2480_, v___x_2482_);
v___x_2485_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2470_, v___f_2475_, v_found_2481_, v___x_2484_);
v___x_2486_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v___x_2485_, v___f_2476_);
v___x_2487_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v___x_2486_, v___f_2483_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2490_, lean_object* v_inst_2491_){
_start:
{
lean_object* v_toApplicative_2492_; lean_object* v_toBind_2493_; lean_object* v_getEnv_2494_; lean_object* v_toPure_2495_; lean_object* v___f_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___f_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; 
v_toApplicative_2492_ = lean_ctor_get(v_inst_2490_, 0);
v_toBind_2493_ = lean_ctor_get(v_inst_2490_, 1);
lean_inc_n(v_toBind_2493_, 3);
v_getEnv_2494_ = lean_ctor_get(v_inst_2491_, 0);
lean_inc(v_getEnv_2494_);
lean_dec_ref(v_inst_2491_);
v_toPure_2495_ = lean_ctor_get(v_toApplicative_2492_, 1);
v___f_2496_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2497_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2498_ = lean_box(1);
v___x_2499_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2495_, 5);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2500_, 0, v_toPure_2495_);
v___f_2501_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2501_, 0, v_toPure_2495_);
v___f_2502_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2502_, 0, v_toPure_2495_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2503_, 0, v_toPure_2495_);
lean_inc_ref(v_inst_2490_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2504_, 0, v_inst_2490_);
lean_closure_set(v___f_2504_, 1, v___f_2502_);
lean_closure_set(v___f_2504_, 2, v_toBind_2493_);
lean_closure_set(v___f_2504_, 3, v___f_2503_);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2505_, 0, v_toPure_2495_);
lean_closure_set(v___f_2505_, 1, v___f_2496_);
lean_closure_set(v___f_2505_, 2, v___f_2497_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2506_, 0, v___x_2499_);
lean_closure_set(v___f_2506_, 1, v_inst_2490_);
lean_closure_set(v___f_2506_, 2, v___f_2504_);
lean_closure_set(v___f_2506_, 3, v_toBind_2493_);
lean_closure_set(v___f_2506_, 4, v___f_2505_);
lean_closure_set(v___f_2506_, 5, v___x_2498_);
lean_closure_set(v___f_2506_, 6, v___f_2501_);
lean_closure_set(v___f_2506_, 7, v___f_2500_);
v___x_2507_ = lean_apply_4(v_toBind_2493_, lean_box(0), lean_box(0), v_getEnv_2494_, v___f_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2509_, v_inst_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2512_, lean_object* v_init_2513_, lean_object* v_x_2514_){
_start:
{
if (lean_obj_tag(v_x_2514_) == 0)
{
lean_object* v_k_2515_; lean_object* v_l_2516_; lean_object* v_r_2517_; lean_object* v___x_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_k_2515_ = lean_ctor_get(v_x_2514_, 1);
v_l_2516_ = lean_ctor_get(v_x_2514_, 3);
v_r_2517_ = lean_ctor_get(v_x_2514_, 4);
lean_inc_n(v_a_2512_, 2);
v___x_2518_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2512_, v_init_2513_, v_l_2516_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
lean_inc(v_k_2515_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2512_);
lean_ctor_set(v___x_2520_, 1, v_k_2515_);
v___x_2521_ = lean_array_push(v_a_2519_, v___x_2520_);
v_init_2513_ = v___x_2521_;
v_x_2514_ = v_r_2517_;
goto _start;
}
else
{
lean_object* v___x_2523_; 
lean_dec(v_a_2512_);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_init_2513_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2524_, lean_object* v_init_2525_, lean_object* v_x_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2524_, v_init_2525_, v_x_2526_);
lean_dec(v_x_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2529_) == 0)
{
lean_object* v_k_2530_; lean_object* v_v_2531_; lean_object* v_l_2532_; lean_object* v_r_2533_; lean_object* v___x_2534_; lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v_a_2537_; 
v_k_2530_ = lean_ctor_get(v_x_2529_, 1);
lean_inc(v_k_2530_);
v_v_2531_ = lean_ctor_get(v_x_2529_, 2);
lean_inc(v_v_2531_);
v_l_2532_ = lean_ctor_get(v_x_2529_, 3);
lean_inc(v_l_2532_);
v_r_2533_ = lean_ctor_get(v_x_2529_, 4);
lean_inc(v_r_2533_);
lean_dec_ref_known(v_x_2529_, 5);
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2528_, v_l_2532_);
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2530_, v_a_2535_, v_v_2531_);
lean_dec(v_v_2531_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v_init_2528_ = v_a_2537_;
v_x_2529_ = v_r_2533_;
goto _start;
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_init_2528_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2540_){
_start:
{
lean_object* v_exported_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; 
v_exported_2541_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2542_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2541_, v_tags_2540_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
return v_a_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2544_, lean_object* v_s_2545_){
_start:
{
lean_object* v_exported_2546_; lean_object* v___x_2547_; lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_exported_2546_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2546_, v_s_2545_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc_n(v_a_2548_, 3);
lean_dec_ref(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2548_);
lean_ctor_set(v___x_2549_, 1, v_a_2548_);
lean_ctor_set(v___x_2549_, 2, v_a_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2550_, lean_object* v_s_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2550_, v_s_2551_);
lean_dec_ref(v_x_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2553_, lean_object* v_k_2554_, lean_object* v_fallback_2555_){
_start:
{
if (lean_obj_tag(v_t_2553_) == 0)
{
lean_object* v_k_2556_; lean_object* v_v_2557_; lean_object* v_l_2558_; lean_object* v_r_2559_; uint8_t v___x_2560_; 
v_k_2556_ = lean_ctor_get(v_t_2553_, 1);
v_v_2557_ = lean_ctor_get(v_t_2553_, 2);
v_l_2558_ = lean_ctor_get(v_t_2553_, 3);
v_r_2559_ = lean_ctor_get(v_t_2553_, 4);
v___x_2560_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2554_, v_k_2556_);
switch(v___x_2560_)
{
case 0:
{
v_t_2553_ = v_l_2558_;
goto _start;
}
case 1:
{
lean_inc(v_v_2557_);
return v_v_2557_;
}
default: 
{
v_t_2553_ = v_r_2559_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2555_);
return v_fallback_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2563_, lean_object* v_k_2564_, lean_object* v_fallback_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2563_, v_k_2564_, v_fallback_2565_);
lean_dec(v_fallback_2565_);
lean_dec(v_k_2564_);
lean_dec(v_t_2563_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2567_, lean_object* v_x_2568_){
_start:
{
lean_object* v_fst_2569_; lean_object* v_snd_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_fst_2569_ = lean_ctor_get(v_x_2568_, 0);
lean_inc(v_fst_2569_);
v_snd_2570_ = lean_ctor_get(v_x_2568_, 1);
lean_inc(v_snd_2570_);
lean_dec_ref(v_x_2568_);
v___x_2571_ = l_Lean_NameSet_empty;
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2567_, v_fst_2569_, v___x_2571_);
v___x_2573_ = l_Lean_NameSet_insert(v___x_2572_, v_snd_2570_);
v___x_2574_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2569_, v___x_2573_, v_tags_2567_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2599_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2602_, lean_object* v_t_2603_, lean_object* v_k_2604_, lean_object* v_fallback_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2603_, v_k_2604_, v_fallback_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2607_, lean_object* v_t_2608_, lean_object* v_k_2609_, lean_object* v_fallback_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2607_, v_t_2608_, v_k_2609_, v_fallback_2610_);
lean_dec(v_fallback_2610_);
lean_dec(v_k_2609_);
lean_dec(v_t_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v_name_2612_, lean_object* v_decl_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2617_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2618_ = l_Lean_MessageData_ofName(v_name_2612_);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_2621_, v___y_2614_, v___y_2615_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_name_2623_, lean_object* v_decl_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v_name_2623_, v_decl_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v_decl_2624_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
if (lean_obj_tag(v_a_2629_) == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = l_List_reverse___redArg(v_a_2630_);
return v___x_2631_;
}
else
{
lean_object* v_head_2632_; lean_object* v_tail_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2645_; 
v_head_2632_ = lean_ctor_get(v_a_2629_, 0);
v_tail_2633_ = lean_ctor_get(v_a_2629_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2629_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2635_ = v_a_2629_;
v_isShared_2636_ = v_isSharedCheck_2645_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_tail_2633_);
lean_inc(v_head_2632_);
lean_dec(v_a_2629_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2645_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2637_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2638_ = l_Lean_MessageData_ofName(v_head_2632_);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2637_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v_a_2630_);
lean_ctor_set(v___x_2635_, 0, v___x_2640_);
v___x_2642_ = v___x_2635_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2630_);
v___x_2642_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v_a_2629_ = v_tail_2633_;
v_a_2630_ = v___x_2642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2646_, lean_object* v_k_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_m_2652_; lean_object* v_a_2653_; uint8_t v___x_2654_; 
v___x_2650_ = lean_nat_add(v_x_2648_, v_x_2649_);
v___x_2651_ = lean_unsigned_to_nat(1u);
v_m_2652_ = lean_nat_shiftr(v___x_2650_, v___x_2651_);
lean_dec(v___x_2650_);
v_a_2653_ = lean_array_fget_borrowed(v_as_2646_, v_m_2652_);
v___x_2654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2653_, v_k_2647_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
lean_dec(v_x_2649_);
v___x_2655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2647_, v_a_2653_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec(v_m_2652_);
lean_dec(v_x_2648_);
lean_inc(v_a_2653_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2653_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_nat_dec_eq(v_m_2652_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = lean_nat_sub(v_m_2652_, v___x_2651_);
lean_dec(v_m_2652_);
v___x_2660_ = lean_nat_dec_lt(v___x_2659_, v_x_2648_);
if (v___x_2660_ == 0)
{
v_x_2649_ = v___x_2659_;
goto _start;
}
else
{
lean_object* v___x_2662_; 
lean_dec(v___x_2659_);
lean_dec(v_x_2648_);
v___x_2662_ = lean_box(0);
return v___x_2662_;
}
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_m_2652_);
lean_dec(v_x_2648_);
v___x_2663_ = lean_box(0);
return v___x_2663_;
}
}
}
else
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
lean_dec(v_x_2648_);
v___x_2664_ = lean_nat_add(v_m_2652_, v___x_2651_);
lean_dec(v_m_2652_);
v___x_2665_ = lean_nat_dec_le(v___x_2664_, v_x_2649_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_dec(v___x_2664_);
lean_dec(v_x_2649_);
v___x_2666_ = lean_box(0);
return v___x_2666_;
}
else
{
v_x_2648_ = v___x_2664_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2668_, lean_object* v_k_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2668_, v_k_2669_, v_x_2670_, v_x_2671_);
lean_dec_ref(v_k_2669_);
lean_dec_ref(v_as_2668_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v_env_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2676_ = lean_st_ref_get(v___y_2674_);
v_env_2680_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_env_2680_);
lean_dec(v___x_2676_);
v___x_2681_ = lean_box(1);
v___x_2682_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2680_, v_tag_2673_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v_toEnvExtension_2684_; lean_object* v_asyncMode_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2683_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2684_ = lean_ctor_get(v___x_2683_, 0);
v_asyncMode_2685_ = lean_ctor_get(v_toEnvExtension_2684_, 2);
v___x_2686_ = lean_box(0);
v___x_2687_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2681_, v___x_2683_, v_env_2680_, v_asyncMode_2685_, v___x_2686_);
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2687_, v_tag_2673_);
lean_dec(v_tag_2673_);
lean_dec(v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
else
{
lean_object* v_val_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2718_; 
v_val_2690_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2692_ = v___x_2682_;
v_isShared_2693_ = v_isSharedCheck_2718_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_val_2690_);
lean_dec(v___x_2682_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2718_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2694_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2695_ = 0;
v___x_2696_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2681_, v___x_2694_, v_env_2680_, v_val_2690_, v___x_2695_);
lean_dec(v_val_2690_);
lean_dec_ref(v_env_2680_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_array_get_size(v___x_2696_);
v___x_2699_ = lean_nat_dec_lt(v___x_2697_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_dec_ref(v___x_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_tag_2673_);
goto v___jp_2677_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_sub(v___x_2698_, v___x_2700_);
v___x_2702_ = lean_nat_dec_le(v___x_2697_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_dec(v___x_2701_);
lean_dec_ref(v___x_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_tag_2673_);
goto v___jp_2677_;
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_tag_2673_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2696_, v___x_2704_, v___x_2697_, v___x_2701_);
lean_dec_ref_known(v___x_2704_, 2);
lean_dec_ref(v___x_2696_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_del_object(v___x_2692_);
goto v___jp_2677_;
}
else
{
lean_object* v_val_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2717_; 
v_val_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2717_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_val_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2717_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_snd_2710_; lean_object* v___x_2712_; 
v_snd_2710_ = lean_ctor_get(v_val_2706_, 1);
lean_inc(v_snd_2710_);
lean_dec(v_val_2706_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v_snd_2710_);
v___x_2712_ = v___x_2708_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_snd_2710_);
v___x_2712_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2714_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2712_);
v___x_2714_ = v___x_2692_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
}
}
v___jp_2677_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2719_, v___y_2720_);
lean_dec(v___y_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2723_, size_t v_sz_2724_, size_t v_i_2725_, lean_object* v_b_2726_){
_start:
{
uint8_t v___x_2728_; 
v___x_2728_ = lean_usize_dec_lt(v_i_2725_, v_sz_2724_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_b_2726_);
return v___x_2729_;
}
else
{
lean_object* v_a_2730_; lean_object* v_fst_2731_; lean_object* v_found_2732_; size_t v___x_2733_; size_t v___x_2734_; 
v_a_2730_ = lean_array_uget_borrowed(v_as_2723_, v_i_2725_);
v_fst_2731_ = lean_ctor_get(v_a_2730_, 0);
lean_inc(v_fst_2731_);
v_found_2732_ = l_Lean_NameSet_insert(v_b_2726_, v_fst_2731_);
v___x_2733_ = ((size_t)1ULL);
v___x_2734_ = lean_usize_add(v_i_2725_, v___x_2733_);
v_i_2725_ = v___x_2734_;
v_b_2726_ = v_found_2732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2736_, lean_object* v_sz_2737_, lean_object* v_i_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2737_);
lean_dec(v_sz_2737_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2738_);
lean_dec(v_i_2738_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2736_, v_sz_boxed_2741_, v_i_boxed_2742_, v_b_2739_);
lean_dec_ref(v_as_2736_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2744_, size_t v_sz_2745_, size_t v_i_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_lt(v_i_2746_, v_sz_2745_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_b_2747_);
return v___x_2752_;
}
else
{
lean_object* v_a_2753_; size_t v_sz_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2753_ = lean_array_uget_borrowed(v_as_2744_, v_i_2746_);
v_sz_2754_ = lean_array_size(v_a_2753_);
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2753_, v_sz_2754_, v___x_2755_, v_b_2747_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; size_t v___x_2758_; size_t v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2746_, v___x_2758_);
v_i_2746_ = v___x_2759_;
v_b_2747_ = v_a_2757_;
goto _start;
}
else
{
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2761_, lean_object* v_sz_2762_, lean_object* v_i_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
size_t v_sz_boxed_2768_; size_t v_i_boxed_2769_; lean_object* v_res_2770_; 
v_sz_boxed_2768_ = lean_unbox_usize(v_sz_2762_);
lean_dec(v_sz_2762_);
v_i_boxed_2769_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2761_, v_sz_boxed_2768_, v_i_boxed_2769_, v_b_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_as_2761_);
return v_res_2770_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2771_, lean_object* v_x1_2772_, lean_object* v_x2_2773_){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2774_ = l_Lean_Name_toString(v_x1_2772_, v___x_2771_);
v___x_2775_ = l_Lean_Name_toString(v_x2_2773_, v___x_2771_);
v___x_2776_ = lean_string_dec_lt(v___x_2774_, v___x_2775_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v___x_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2777_, lean_object* v_x1_2778_, lean_object* v_x2_2779_){
_start:
{
uint8_t v___x_7611__boxed_2780_; uint8_t v_res_2781_; lean_object* v_r_2782_; 
v___x_7611__boxed_2780_ = lean_unbox(v___x_2777_);
v_res_2781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_7611__boxed_2780_, v_x1_2778_, v_x2_2779_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object* v_hi_2783_, lean_object* v_pivot_2784_, lean_object* v_as_2785_, lean_object* v_i_2786_, lean_object* v_k_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_nat_dec_lt(v_k_2787_, v_hi_2783_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec(v_k_2787_);
lean_dec(v_pivot_2784_);
v___x_2789_ = lean_array_fswap(v_as_2785_, v_i_2786_, v_hi_2783_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_i_2786_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2791_ = lean_array_fget_borrowed(v_as_2785_, v_k_2787_);
lean_inc(v___x_2791_);
v___x_2792_ = l_Lean_Name_toString(v___x_2791_, v___x_2788_);
lean_inc(v_pivot_2784_);
v___x_2793_ = l_Lean_Name_toString(v_pivot_2784_, v___x_2788_);
v___x_2794_ = lean_string_dec_lt(v___x_2792_, v___x_2793_);
lean_dec_ref(v___x_2793_);
lean_dec_ref(v___x_2792_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_nat_add(v_k_2787_, v___x_2795_);
lean_dec(v_k_2787_);
v_k_2787_ = v___x_2796_;
goto _start;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2798_ = lean_array_fswap(v_as_2785_, v_i_2786_, v_k_2787_);
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_nat_add(v_i_2786_, v___x_2799_);
lean_dec(v_i_2786_);
v___x_2801_ = lean_nat_add(v_k_2787_, v___x_2799_);
lean_dec(v_k_2787_);
v_as_2785_ = v___x_2798_;
v_i_2786_ = v___x_2800_;
v_k_2787_ = v___x_2801_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_hi_2803_, lean_object* v_pivot_2804_, lean_object* v_as_2805_, lean_object* v_i_2806_, lean_object* v_k_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2803_, v_pivot_2804_, v_as_2805_, v_i_2806_, v_k_2807_);
lean_dec(v_hi_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_n_2809_, lean_object* v_as_2810_, lean_object* v_lo_2811_, lean_object* v_hi_2812_){
_start:
{
lean_object* v___y_2814_; uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_lt(v_lo_2811_, v_hi_2812_);
if (v___x_2824_ == 0)
{
lean_dec(v_lo_2811_);
return v_as_2810_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v_mid_2827_; lean_object* v___y_2829_; lean_object* v___y_2835_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2825_ = lean_nat_add(v_lo_2811_, v_hi_2812_);
v___x_2826_ = lean_unsigned_to_nat(1u);
v_mid_2827_ = lean_nat_shiftr(v___x_2825_, v___x_2826_);
lean_dec(v___x_2825_);
v___x_2840_ = lean_array_fget_borrowed(v_as_2810_, v_mid_2827_);
v___x_2841_ = lean_array_fget_borrowed(v_as_2810_, v_lo_2811_);
lean_inc(v___x_2841_);
lean_inc(v___x_2840_);
v___x_2842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2824_, v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
v___y_2835_ = v_as_2810_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_array_fswap(v_as_2810_, v_lo_2811_, v_mid_2827_);
v___y_2835_ = v___x_2843_;
goto v___jp_2834_;
}
v___jp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2830_ = lean_array_fget_borrowed(v___y_2829_, v_mid_2827_);
v___x_2831_ = lean_array_fget_borrowed(v___y_2829_, v_hi_2812_);
lean_inc(v___x_2831_);
lean_inc(v___x_2830_);
v___x_2832_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2824_, v___x_2830_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_dec(v_mid_2827_);
v___y_2814_ = v___y_2829_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_array_fswap(v___y_2829_, v_mid_2827_, v_hi_2812_);
lean_dec(v_mid_2827_);
v___y_2814_ = v___x_2833_;
goto v___jp_2813_;
}
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = lean_array_fget_borrowed(v___y_2835_, v_hi_2812_);
v___x_2837_ = lean_array_fget_borrowed(v___y_2835_, v_lo_2811_);
lean_inc(v___x_2837_);
lean_inc(v___x_2836_);
v___x_2838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2824_, v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
v___y_2829_ = v___y_2835_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_array_fswap(v___y_2835_, v_lo_2811_, v_hi_2812_);
v___y_2829_ = v___x_2839_;
goto v___jp_2828_;
}
}
}
v___jp_2813_:
{
lean_object* v_pivot_2815_; lean_object* v___x_2816_; lean_object* v_fst_2817_; lean_object* v_snd_2818_; uint8_t v___x_2819_; 
v_pivot_2815_ = lean_array_fget(v___y_2814_, v_hi_2812_);
lean_inc_n(v_lo_2811_, 2);
v___x_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2812_, v_pivot_2815_, v___y_2814_, v_lo_2811_, v_lo_2811_);
v_fst_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_fst_2817_);
v_snd_2818_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_snd_2818_);
lean_dec_ref(v___x_2816_);
v___x_2819_ = lean_nat_dec_le(v_hi_2812_, v_fst_2817_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2809_, v_snd_2818_, v_lo_2811_, v_fst_2817_);
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_2822_ = lean_nat_add(v_fst_2817_, v___x_2821_);
lean_dec(v_fst_2817_);
v_as_2810_ = v___x_2820_;
v_lo_2811_ = v___x_2822_;
goto _start;
}
else
{
lean_dec(v_fst_2817_);
lean_dec(v_lo_2811_);
return v_snd_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_n_2844_, lean_object* v_as_2845_, lean_object* v_lo_2846_, lean_object* v_hi_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2844_, v_as_2845_, v_lo_2846_, v_hi_2847_);
lean_dec(v_hi_2847_);
lean_dec(v_n_2844_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2849_, lean_object* v_x_2850_){
_start:
{
if (lean_obj_tag(v_x_2850_) == 0)
{
lean_object* v_k_2852_; lean_object* v_l_2853_; lean_object* v_r_2854_; lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v_a_2857_; lean_object* v___x_2858_; 
v_k_2852_ = lean_ctor_get(v_x_2850_, 1);
lean_inc(v_k_2852_);
v_l_2853_ = lean_ctor_get(v_x_2850_, 3);
lean_inc(v_l_2853_);
v_r_2854_ = lean_ctor_get(v_x_2850_, 4);
lean_inc(v_r_2854_);
lean_dec_ref_known(v_x_2850_, 5);
v___x_2855_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2849_, v_l_2853_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v_a_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc(v_a_2857_);
lean_dec(v_a_2856_);
v___x_2858_ = l_Lean_NameSet_insert(v_a_2857_, v_k_2852_);
v_init_2849_ = v___x_2858_;
v_x_2850_ = v_r_2854_;
goto _start;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_init_2849_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2862_, lean_object* v_x_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2862_, v_x_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2866_, lean_object* v_x_2867_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 0)
{
lean_object* v_k_2868_; lean_object* v_l_2869_; lean_object* v_r_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_k_2868_ = lean_ctor_get(v_x_2867_, 1);
lean_inc(v_k_2868_);
v_l_2869_ = lean_ctor_get(v_x_2867_, 3);
lean_inc(v_l_2869_);
v_r_2870_ = lean_ctor_get(v_x_2867_, 4);
lean_inc(v_r_2870_);
lean_dec_ref_known(v_x_2867_, 5);
v___x_2871_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2866_, v_l_2869_);
v___x_2872_ = lean_array_push(v___x_2871_, v_k_2868_);
v_init_2866_ = v___x_2872_;
v_x_2867_ = v_r_2870_;
goto _start;
}
else
{
return v_init_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___y_2878_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___x_2904_; lean_object* v_env_2905_; lean_object* v___x_2906_; lean_object* v_toEnvExtension_2907_; lean_object* v_asyncMode_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_found_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v_a_2915_; lean_object* v_a_2917_; lean_object* v_a_2934_; 
v___x_2904_ = lean_st_ref_get(v___y_2875_);
v_env_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc_ref_n(v_env_2905_, 2);
lean_dec(v___x_2904_);
v___x_2906_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2907_ = lean_ctor_get(v___x_2906_, 0);
v_asyncMode_2908_ = lean_ctor_get(v_toEnvExtension_2907_, 2);
v___x_2909_ = lean_box(1);
v___x_2910_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
v_found_2911_ = l_Lean_NameSet_empty;
v___x_2912_ = lean_box(0);
v___x_2913_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2909_, v___x_2906_, v_env_2905_, v_asyncMode_2908_, v___x_2912_);
v___x_2914_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2911_, v___x_2913_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v_a_2934_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_a_2934_);
lean_dec(v_a_2915_);
v_a_2917_ = v_a_2934_;
goto v___jp_2916_;
v___jp_2877_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_array_to_list(v___y_2878_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
v___jp_2881_:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2882_, v___y_2884_, v___y_2883_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec(v___y_2882_);
v___y_2878_ = v___x_2886_;
goto v___jp_2877_;
}
v___jp_2887_:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_nat_dec_le(v___y_2891_, v___y_2888_);
if (v___x_2892_ == 0)
{
lean_dec(v___y_2888_);
lean_inc(v___y_2891_);
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___y_2891_;
v___y_2884_ = v___y_2890_;
v___y_2885_ = v___y_2891_;
goto v___jp_2881_;
}
else
{
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___y_2891_;
v___y_2884_ = v___y_2890_;
v___y_2885_ = v___y_2888_;
goto v___jp_2881_;
}
}
v___jp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2896_ = lean_mk_empty_array_with_capacity(v___y_2895_);
lean_dec(v___y_2895_);
v___x_2897_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2896_, v___y_2894_);
v___x_2898_ = lean_array_get_size(v___x_2897_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_nat_dec_eq(v___x_2898_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_nat_sub(v___x_2898_, v___x_2901_);
v___x_2903_ = lean_nat_dec_le(v___x_2899_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_inc(v___x_2902_);
v___y_2888_ = v___x_2902_;
v___y_2889_ = v___x_2898_;
v___y_2890_ = v___x_2897_;
v___y_2891_ = v___x_2902_;
goto v___jp_2887_;
}
else
{
v___y_2888_ = v___x_2902_;
v___y_2889_ = v___x_2898_;
v___y_2890_ = v___x_2897_;
v___y_2891_ = v___x_2899_;
goto v___jp_2887_;
}
}
else
{
v___y_2878_ = v___x_2897_;
goto v___jp_2877_;
}
}
v___jp_2916_:
{
lean_object* v___x_2918_; lean_object* v_importedEntries_2919_; size_t v_sz_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2918_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2910_, v_toEnvExtension_2907_, v_env_2905_, v_asyncMode_2908_, v___x_2912_);
v_importedEntries_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_importedEntries_2919_);
lean_dec(v___x_2918_);
v_sz_2920_ = lean_array_size(v_importedEntries_2919_);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2919_, v_sz_2920_, v___x_2921_, v_a_2917_, v___y_2874_, v___y_2875_);
lean_dec_ref(v_importedEntries_2919_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
if (lean_obj_tag(v_a_2923_) == 0)
{
lean_object* v_size_2924_; 
v_size_2924_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_size_2924_);
v___y_2894_ = v_a_2923_;
v___y_2895_ = v_size_2924_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_unsigned_to_nat(0u);
v___y_2894_ = v_a_2923_;
v___y_2895_ = v___x_2925_;
goto v___jp_2893_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_a_2926_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2922_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2941_ = l_Lean_stringToMessageData(v___x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2957_ = l_Lean_MessageData_ofFormat(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2962_ = l_Lean_MessageData_ofFormat(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2965_ = l_Lean_stringToMessageData(v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2966_, lean_object* v_as_2967_, size_t v_sz_2968_, size_t v_i_2969_, lean_object* v_b_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_a_2975_; uint8_t v___x_2979_; 
v___x_2979_ = lean_usize_dec_lt(v_i_2969_, v_sz_2968_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_decl_2966_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2970_);
return v___x_2980_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2981_ = lean_array_uget_borrowed(v_as_2967_, v_i_2969_);
v___x_2982_ = l_Lean_TSyntax_getId(v_a_2981_);
lean_inc(v___x_2982_);
v___x_2983_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2982_, v___y_2972_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = lean_box(0);
if (lean_obj_tag(v_a_2984_) == 1)
{
lean_object* v___x_2986_; lean_object* v_env_2987_; lean_object* v_nextMacroScope_2988_; lean_object* v_ngen_2989_; lean_object* v_auxDeclNGen_2990_; lean_object* v_traceState_2991_; lean_object* v_messages_2992_; lean_object* v_infoState_2993_; lean_object* v_snapshotTasks_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref_known(v_a_2984_, 1);
v___x_2986_ = lean_st_ref_take(v___y_2972_);
v_env_2987_ = lean_ctor_get(v___x_2986_, 0);
v_nextMacroScope_2988_ = lean_ctor_get(v___x_2986_, 1);
v_ngen_2989_ = lean_ctor_get(v___x_2986_, 2);
v_auxDeclNGen_2990_ = lean_ctor_get(v___x_2986_, 3);
v_traceState_2991_ = lean_ctor_get(v___x_2986_, 4);
v_messages_2992_ = lean_ctor_get(v___x_2986_, 6);
v_infoState_2993_ = lean_ctor_get(v___x_2986_, 7);
v_snapshotTasks_2994_ = lean_ctor_get(v___x_2986_, 8);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v___x_2986_, 5);
lean_dec(v_unused_3010_);
v___x_2996_ = v___x_2986_;
v_isShared_2997_ = v_isSharedCheck_3009_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_snapshotTasks_2994_);
lean_inc(v_infoState_2993_);
lean_inc(v_messages_2992_);
lean_inc(v_traceState_2991_);
lean_inc(v_auxDeclNGen_2990_);
lean_inc(v_ngen_2989_);
lean_inc(v_nextMacroScope_2988_);
lean_inc(v_env_2987_);
lean_dec(v___x_2986_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3009_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v_toEnvExtension_2999_; lean_object* v_asyncMode_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_2998_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2999_ = lean_ctor_get(v___x_2998_, 0);
v_asyncMode_3000_ = lean_ctor_get(v_toEnvExtension_2999_, 2);
v___x_3001_ = lean_box(0);
lean_inc(v_decl_2966_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_decl_2966_);
lean_ctor_set(v___x_3002_, 1, v___x_2982_);
v___x_3003_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2998_, v_env_2987_, v___x_3002_, v_asyncMode_3000_, v___x_3001_);
v___x_3004_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 5, v___x_3004_);
lean_ctor_set(v___x_2996_, 0, v___x_3003_);
v___x_3006_ = v___x_2996_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_nextMacroScope_2988_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_ngen_2989_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_auxDeclNGen_2990_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_traceState_2991_);
lean_ctor_set(v_reuseFailAlloc_3008_, 5, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3008_, 6, v_messages_2992_);
lean_ctor_set(v_reuseFailAlloc_3008_, 7, v_infoState_2993_);
lean_ctor_set(v_reuseFailAlloc_3008_, 8, v_snapshotTasks_2994_);
v___x_3006_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_st_ref_set(v___y_2972_, v___x_3006_);
v_a_2975_ = v___x_2985_;
goto v___jp_2974_;
}
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_a_2984_);
v___x_3011_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___y_3014_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = l_List_lengthTR___redArg(v_a_3012_);
v___x_3028_ = lean_nat_dec_eq(v___x_3027_, v___x_3026_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = lean_unsigned_to_nat(1u);
v___x_3030_ = lean_nat_dec_eq(v___x_3027_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_unsigned_to_nat(10u);
v___x_3032_ = lean_nat_dec_lt(v___x_3027_, v___x_3031_);
lean_dec(v___x_3027_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_3012_);
v___x_3035_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_3012_, v_a_3012_, v___x_3031_, v___x_3034_);
lean_dec(v_a_3012_);
v___x_3036_ = lean_box(0);
v___x_3037_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_3035_, v___x_3036_);
v___x_3038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3039_ = l_Lean_MessageData_joinSep(v___x_3037_, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3033_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___y_3014_ = v___x_3042_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3044_ = lean_box(0);
v___x_3045_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3012_, v___x_3044_);
v___x_3046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3047_ = l_Lean_MessageData_joinSep(v___x_3045_, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3043_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___y_3014_ = v___x_3048_;
goto v___jp_3013_;
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec(v___x_3027_);
v___x_3049_ = lean_box(0);
v___x_3050_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3012_, v___x_3049_);
v___x_3051_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3052_ = l_Lean_MessageData_joinSep(v___x_3050_, v___x_3051_);
v___y_3014_ = v___x_3052_;
goto v___jp_3013_;
}
}
else
{
lean_object* v___x_3053_; 
lean_dec(v___x_3027_);
lean_dec(v_a_3012_);
v___x_3053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_3014_ = v___x_3053_;
goto v___jp_3013_;
}
v___jp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___y_3014_);
v___x_3017_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_3020_ = l_Lean_MessageData_ofName(v___x_2982_);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___x_3018_);
v___x_3025_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_a_2981_, v___x_3024_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_dec_ref_known(v___x_3025_, 1);
v_a_2975_ = v___x_2985_;
goto v___jp_2974_;
}
else
{
lean_dec(v_decl_2966_);
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v___x_2982_);
lean_dec(v_decl_2966_);
v_a_3054_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3011_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3011_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_2982_);
lean_dec(v_decl_2966_);
v_a_3062_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2983_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2983_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
v___jp_2974_:
{
size_t v___x_2976_; size_t v___x_2977_; 
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_add(v_i_2969_, v___x_2976_);
v_i_2969_ = v___x_2977_;
v_b_2970_ = v_a_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_3070_, lean_object* v_as_3071_, lean_object* v_sz_3072_, lean_object* v_i_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
size_t v_sz_boxed_3078_; size_t v_i_boxed_3079_; lean_object* v_res_3080_; 
v_sz_boxed_3078_ = lean_unbox_usize(v_sz_3072_);
lean_dec(v_sz_3072_);
v_i_boxed_3079_ = lean_unbox_usize(v_i_3073_);
lean_dec(v_i_3073_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3070_, v_as_3071_, v_sz_boxed_3078_, v_i_boxed_3079_, v_b_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v_as_3071_);
return v_res_3080_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3083_ = l_Lean_stringToMessageData(v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_3084_, lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v_name_3087_, lean_object* v_decl_3088_, lean_object* v_stx_3089_, uint8_t v_kind_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = 0;
v___x_3155_ = l_Lean_instBEqAttributeKind_beq(v_kind_3090_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec(v_stx_3089_);
lean_dec(v_decl_3088_);
lean_dec_ref(v___x_3086_);
lean_dec_ref(v___x_3085_);
lean_dec_ref(v___x_3084_);
v___x_3156_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_3087_, v_kind_3090_, v___y_3091_, v___y_3092_);
return v___x_3156_;
}
else
{
goto v___jp_3128_;
}
v___jp_3094_:
{
lean_object* v___x_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_box(0);
v_sz_3099_ = lean_array_size(v___y_3095_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3088_, v___y_3095_, v_sz_3099_, v___x_3100_, v___x_3098_, v___y_3096_, v___y_3097_);
lean_dec_ref(v___y_3095_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v___x_3101_, 0);
lean_dec(v_unused_3109_);
v___x_3103_ = v___x_3101_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_dec(v___x_3101_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3098_);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3098_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
return v___x_3101_;
}
}
v___jp_3110_:
{
lean_object* v___x_3114_; lean_object* v_env_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_st_ref_get(v___y_3113_);
v_env_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc_ref(v_env_3115_);
lean_dec(v___x_3114_);
lean_inc(v_decl_3088_);
v___x_3116_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3115_, v_decl_3088_);
if (lean_obj_tag(v___x_3116_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec_ref(v___y_3111_);
v_val_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3119_ = 0;
v___x_3120_ = l_Lean_MessageData_ofConstName(v_decl_3088_, v___x_3119_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3118_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_MessageData_ofConstName(v_val_3117_, v___x_3119_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3118_);
v___x_3127_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3089_, v___x_3126_, v___y_3112_, v___y_3113_);
lean_dec(v_stx_3089_);
return v___x_3127_;
}
else
{
lean_dec(v___x_3116_);
lean_dec(v_stx_3089_);
v___y_3095_ = v___y_3111_;
v___y_3096_ = v___y_3112_;
v___y_3097_ = v___y_3113_;
goto v___jp_3094_;
}
}
v___jp_3128_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_3130_ = l_Lean_Name_mkStr4(v___x_3084_, v___x_3085_, v___x_3129_, v___x_3086_);
lean_inc(v_stx_3089_);
v___x_3131_ = l_Lean_Syntax_isOfKind(v_stx_3089_, v___x_3130_);
lean_dec(v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_stx_3089_);
lean_dec(v_decl_3088_);
v___x_3132_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3133_ = l_Lean_MessageData_ofName(v_name_3087_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_3136_, v___y_3091_, v___y_3092_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; lean_object* v_env_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_tags_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v_name_3087_);
v___x_3138_ = lean_st_ref_get(v___y_3092_);
v_env_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3139_);
lean_dec(v___x_3138_);
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = l_Lean_Syntax_getArg(v_stx_3089_, v___x_3140_);
v_tags_3142_ = l_Lean_Syntax_getArgs(v___x_3141_);
lean_dec(v___x_3141_);
v___x_3143_ = 0;
lean_inc(v_decl_3088_);
v___x_3144_ = l_Lean_Environment_find_x3f(v_env_3139_, v_decl_3088_, v___x_3143_);
if (lean_obj_tag(v___x_3144_) == 0)
{
v___y_3111_ = v_tags_3142_;
v___y_3112_ = v___y_3091_;
v___y_3113_ = v___y_3092_;
goto v___jp_3110_;
}
else
{
lean_dec_ref_known(v___x_3144_, 1);
if (v___x_3131_ == 0)
{
v___y_3111_ = v_tags_3142_;
v___y_3112_ = v___y_3091_;
v___y_3113_ = v___y_3092_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3145_; lean_object* v_env_3146_; uint8_t v___x_3147_; 
v___x_3145_ = lean_st_ref_get(v___y_3092_);
v_env_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc_ref(v_env_3146_);
lean_dec(v___x_3145_);
v___x_3147_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_3146_, v_decl_3088_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec_ref(v_tags_3142_);
v___x_3148_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3149_ = l_Lean_MessageData_ofConstName(v_decl_3088_, v___x_3143_);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3089_, v___x_3152_, v___y_3091_, v___y_3092_);
lean_dec(v_stx_3089_);
return v___x_3153_;
}
else
{
v___y_3111_ = v_tags_3142_;
v___y_3112_ = v___y_3091_;
v___y_3113_ = v___y_3092_;
goto v___jp_3110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_name_3160_, lean_object* v_decl_3161_, lean_object* v_stx_3162_, lean_object* v_kind_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v_kind_boxed_3167_; lean_object* v_res_3168_; 
v_kind_boxed_3167_ = lean_unbox(v_kind_3163_);
v_res_3168_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_3157_, v___x_3158_, v___x_3159_, v_name_3160_, v_decl_3161_, v_stx_3162_, v_kind_boxed_3167_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3203_ = l_Lean_registerBuiltinAttribute(v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_3206_, v___y_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_3216_, lean_object* v_k_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3216_, v_k_3217_, v_x_3218_, v_x_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_3222_, lean_object* v_k_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_3222_, v_k_3223_, v_x_3224_, v_x_3225_, v_x_3226_);
lean_dec_ref(v_k_3223_);
lean_dec_ref(v_as_3222_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_3228_, size_t v_sz_3229_, size_t v_i_3230_, lean_object* v_b_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_3228_, v_sz_3229_, v_i_3230_, v_b_3231_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_3236_, lean_object* v_sz_3237_, lean_object* v_i_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_sz_boxed_3243_; size_t v_i_boxed_3244_; lean_object* v_res_3245_; 
v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3237_);
lean_dec(v_sz_3237_);
v_i_boxed_3244_ = lean_unbox_usize(v_i_3238_);
lean_dec(v_i_3238_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_3236_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v_as_3236_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_3246_, lean_object* v_t_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_3246_, v_t_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_3249_, lean_object* v_as_3250_, lean_object* v_lo_3251_, lean_object* v_hi_3252_, lean_object* v_w_3253_, lean_object* v_hlo_3254_, lean_object* v_hhi_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_3249_, v_as_3250_, v_lo_3251_, v_hi_3252_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_3257_, lean_object* v_as_3258_, lean_object* v_lo_3259_, lean_object* v_hi_3260_, lean_object* v_w_3261_, lean_object* v_hlo_3262_, lean_object* v_hhi_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_3257_, v_as_3258_, v_lo_3259_, v_hi_3260_, v_w_3261_, v_hlo_3262_, v_hhi_3263_);
lean_dec(v_hi_3260_);
lean_dec(v_n_3257_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_3265_, lean_object* v_x_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_3265_, v_x_3266_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_3271_, lean_object* v_x_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_3271_, v_x_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object* v_n_3277_, lean_object* v_lo_3278_, lean_object* v_hi_3279_, lean_object* v_hhi_3280_, lean_object* v_pivot_3281_, lean_object* v_as_3282_, lean_object* v_i_3283_, lean_object* v_k_3284_, lean_object* v_ilo_3285_, lean_object* v_ik_3286_, lean_object* v_w_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_3279_, v_pivot_3281_, v_as_3282_, v_i_3283_, v_k_3284_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object* v_n_3289_, lean_object* v_lo_3290_, lean_object* v_hi_3291_, lean_object* v_hhi_3292_, lean_object* v_pivot_3293_, lean_object* v_as_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_, lean_object* v_ilo_3297_, lean_object* v_ik_3298_, lean_object* v_w_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(v_n_3289_, v_lo_3290_, v_hi_3291_, v_hhi_3292_, v_pivot_3293_, v_as_3294_, v_i_3295_, v_k_3296_, v_ilo_3297_, v_ik_3298_, v_w_3299_);
lean_dec(v_hi_3291_);
lean_dec(v_lo_3290_);
lean_dec(v_n_3289_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_fst_3305_ = lean_ctor_get(v_x_3304_, 0);
lean_inc(v_fst_3305_);
v_snd_3306_ = lean_ctor_get(v_x_3304_, 1);
lean_inc(v_snd_3306_);
lean_dec_ref(v_x_3304_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3308_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3303_, v_fst_3305_, v___x_3307_);
v___x_3309_ = lean_array_push(v___x_3308_, v_snd_3306_);
v___x_3310_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3305_, v___x_3309_, v_es_3303_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3311_, lean_object* v_x_3312_){
_start:
{
if (lean_obj_tag(v_x_3312_) == 0)
{
lean_object* v_k_3313_; lean_object* v_v_3314_; lean_object* v_l_3315_; lean_object* v_r_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_k_3313_ = lean_ctor_get(v_x_3312_, 1);
v_v_3314_ = lean_ctor_get(v_x_3312_, 2);
v_l_3315_ = lean_ctor_get(v_x_3312_, 3);
v_r_3316_ = lean_ctor_get(v_x_3312_, 4);
v___x_3317_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3311_, v_l_3315_);
lean_inc(v_v_3314_);
lean_inc(v_k_3313_);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_k_3313_);
lean_ctor_set(v___x_3318_, 1, v_v_3314_);
v___x_3319_ = lean_array_push(v___x_3317_, v___x_3318_);
v_init_3311_ = v___x_3319_;
v_x_3312_ = v_r_3316_;
goto _start;
}
else
{
return v_init_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3321_, lean_object* v_x_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3321_, v_x_3322_);
lean_dec(v_x_3322_);
return v_res_3323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3324_, lean_object* v_x2_3325_){
_start:
{
lean_object* v_fst_3326_; lean_object* v_fst_3327_; uint8_t v___x_3328_; 
v_fst_3326_ = lean_ctor_get(v_x1_3324_, 0);
v_fst_3327_ = lean_ctor_get(v_x2_3325_, 0);
v___x_3328_ = l_Lean_Name_quickLt(v_fst_3326_, v_fst_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3329_, lean_object* v_x2_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3329_, v_x2_3330_);
lean_dec_ref(v_x2_3330_);
lean_dec_ref(v_x1_3329_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3333_, lean_object* v_pivot_3334_, lean_object* v_as_3335_, lean_object* v_i_3336_, lean_object* v_k_3337_){
_start:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_lt(v_k_3337_, v_hi_3333_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec(v_k_3337_);
v___x_3339_ = lean_array_fswap(v_as_3335_, v_i_3336_, v_hi_3333_);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v_i_3336_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
return v___x_3340_;
}
else
{
lean_object* v___x_3341_; lean_object* v_fst_3342_; lean_object* v_fst_3343_; uint8_t v___x_3344_; 
v___x_3341_ = lean_array_fget_borrowed(v_as_3335_, v_k_3337_);
v_fst_3342_ = lean_ctor_get(v___x_3341_, 0);
v_fst_3343_ = lean_ctor_get(v_pivot_3334_, 0);
v___x_3344_ = l_Lean_Name_quickLt(v_fst_3342_, v_fst_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_nat_add(v_k_3337_, v___x_3345_);
lean_dec(v_k_3337_);
v_k_3337_ = v___x_3346_;
goto _start;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = lean_array_fswap(v_as_3335_, v_i_3336_, v_k_3337_);
v___x_3349_ = lean_unsigned_to_nat(1u);
v___x_3350_ = lean_nat_add(v_i_3336_, v___x_3349_);
lean_dec(v_i_3336_);
v___x_3351_ = lean_nat_add(v_k_3337_, v___x_3349_);
lean_dec(v_k_3337_);
v_as_3335_ = v___x_3348_;
v_i_3336_ = v___x_3350_;
v_k_3337_ = v___x_3351_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3353_, lean_object* v_pivot_3354_, lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_k_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3353_, v_pivot_3354_, v_as_3355_, v_i_3356_, v_k_3357_);
lean_dec_ref(v_pivot_3354_);
lean_dec(v_hi_3353_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3359_, lean_object* v_as_3360_, lean_object* v_lo_3361_, lean_object* v_hi_3362_){
_start:
{
lean_object* v___y_3364_; uint8_t v___x_3374_; 
v___x_3374_ = lean_nat_dec_lt(v_lo_3361_, v_hi_3362_);
if (v___x_3374_ == 0)
{
lean_dec(v_lo_3361_);
return v_as_3360_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v_mid_3377_; lean_object* v___y_3379_; lean_object* v___y_3385_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3375_ = lean_nat_add(v_lo_3361_, v_hi_3362_);
v___x_3376_ = lean_unsigned_to_nat(1u);
v_mid_3377_ = lean_nat_shiftr(v___x_3375_, v___x_3376_);
lean_dec(v___x_3375_);
v___x_3390_ = lean_array_fget_borrowed(v_as_3360_, v_mid_3377_);
v___x_3391_ = lean_array_fget_borrowed(v_as_3360_, v_lo_3361_);
v___x_3392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
v___y_3385_ = v_as_3360_;
goto v___jp_3384_;
}
else
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_array_fswap(v_as_3360_, v_lo_3361_, v_mid_3377_);
v___y_3385_ = v___x_3393_;
goto v___jp_3384_;
}
v___jp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = lean_array_fget_borrowed(v___y_3379_, v_mid_3377_);
v___x_3381_ = lean_array_fget_borrowed(v___y_3379_, v_hi_3362_);
v___x_3382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_dec(v_mid_3377_);
v___y_3364_ = v___y_3379_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_array_fswap(v___y_3379_, v_mid_3377_, v_hi_3362_);
lean_dec(v_mid_3377_);
v___y_3364_ = v___x_3383_;
goto v___jp_3363_;
}
}
v___jp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3386_ = lean_array_fget_borrowed(v___y_3385_, v_hi_3362_);
v___x_3387_ = lean_array_fget_borrowed(v___y_3385_, v_lo_3361_);
v___x_3388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
v___y_3379_ = v___y_3385_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_array_fswap(v___y_3385_, v_lo_3361_, v_hi_3362_);
v___y_3379_ = v___x_3389_;
goto v___jp_3378_;
}
}
}
v___jp_3363_:
{
lean_object* v_pivot_3365_; lean_object* v___x_3366_; lean_object* v_fst_3367_; lean_object* v_snd_3368_; uint8_t v___x_3369_; 
v_pivot_3365_ = lean_array_fget(v___y_3364_, v_hi_3362_);
lean_inc_n(v_lo_3361_, 2);
v___x_3366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3362_, v_pivot_3365_, v___y_3364_, v_lo_3361_, v_lo_3361_);
lean_dec(v_pivot_3365_);
v_fst_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_fst_3367_);
v_snd_3368_ = lean_ctor_get(v___x_3366_, 1);
lean_inc(v_snd_3368_);
lean_dec_ref(v___x_3366_);
v___x_3369_ = lean_nat_dec_le(v_hi_3362_, v_fst_3367_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3359_, v_snd_3368_, v_lo_3361_, v_fst_3367_);
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_add(v_fst_3367_, v___x_3371_);
lean_dec(v_fst_3367_);
v_as_3360_ = v___x_3370_;
v_lo_3361_ = v___x_3372_;
goto _start;
}
else
{
lean_dec(v_fst_3367_);
lean_dec(v_lo_3361_);
return v_snd_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3394_, lean_object* v_as_3395_, lean_object* v_lo_3396_, lean_object* v_hi_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3394_, v_as_3395_, v_lo_3396_, v_hi_3397_);
lean_dec(v_hi_3397_);
lean_dec(v_n_3394_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3401_, lean_object* v_s_3402_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___x_3412_; 
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3405_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3404_, v_s_3402_);
v___x_3406_ = lean_array_get_size(v___x_3405_);
v___x_3412_ = lean_nat_dec_eq(v___x_3406_, v___x_3403_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___y_3416_; uint8_t v___x_3418_; 
v___x_3413_ = lean_unsigned_to_nat(1u);
v___x_3414_ = lean_nat_sub(v___x_3406_, v___x_3413_);
v___x_3418_ = lean_nat_dec_le(v___x_3403_, v___x_3414_);
if (v___x_3418_ == 0)
{
lean_inc(v___x_3414_);
v___y_3416_ = v___x_3414_;
goto v___jp_3415_;
}
else
{
v___y_3416_ = v___x_3403_;
goto v___jp_3415_;
}
v___jp_3415_:
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_nat_dec_le(v___y_3416_, v___x_3414_);
if (v___x_3417_ == 0)
{
lean_dec(v___x_3414_);
lean_inc(v___y_3416_);
v___y_3408_ = v___y_3416_;
v___y_3409_ = v___y_3416_;
goto v___jp_3407_;
}
else
{
v___y_3408_ = v___y_3416_;
v___y_3409_ = v___x_3414_;
goto v___jp_3407_;
}
}
}
else
{
lean_object* v___x_3419_; 
lean_inc_ref_n(v___x_3405_, 2);
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3405_);
lean_ctor_set(v___x_3419_, 1, v___x_3405_);
lean_ctor_set(v___x_3419_, 2, v___x_3405_);
return v___x_3419_;
}
v___jp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3406_, v___x_3405_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_inc_ref_n(v___x_3410_, 2);
v___x_3411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
lean_ctor_set(v___x_3411_, 2, v___x_3410_);
return v___x_3411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3420_, lean_object* v_s_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3420_, v_s_3421_);
lean_dec(v_s_3421_);
lean_dec_ref(v_x_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3423_){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3424_ = lean_unsigned_to_nat(0u);
v___x_3425_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3426_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3425_, v_es_3423_);
v___x_3427_ = lean_array_get_size(v___x_3426_);
v___x_3428_ = lean_nat_dec_eq(v___x_3427_, v___x_3424_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___y_3432_; uint8_t v___x_3436_; 
v___x_3429_ = lean_unsigned_to_nat(1u);
v___x_3430_ = lean_nat_sub(v___x_3427_, v___x_3429_);
v___x_3436_ = lean_nat_dec_le(v___x_3424_, v___x_3430_);
if (v___x_3436_ == 0)
{
lean_inc(v___x_3430_);
v___y_3432_ = v___x_3430_;
goto v___jp_3431_;
}
else
{
v___y_3432_ = v___x_3424_;
goto v___jp_3431_;
}
v___jp_3431_:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_nat_dec_le(v___y_3432_, v___x_3430_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_dec(v___x_3430_);
lean_inc(v___y_3432_);
v___x_3434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3427_, v___x_3426_, v___y_3432_, v___y_3432_);
lean_dec(v___y_3432_);
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; 
v___x_3435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3427_, v___x_3426_, v___y_3432_, v___x_3430_);
lean_dec(v___x_3430_);
return v___x_3435_;
}
}
}
else
{
return v___x_3426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3437_);
lean_dec(v_es_3437_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3439_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3444_, lean_object* v_x_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3444_, v_x_3445_, v___y_3446_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v_x_3445_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3475_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3478_, lean_object* v_t_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3478_, v_t_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3481_, lean_object* v_t_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3481_, v_t_3482_);
lean_dec(v_t_3482_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3484_, lean_object* v_as_3485_, lean_object* v_lo_3486_, lean_object* v_hi_3487_, lean_object* v_w_3488_, lean_object* v_hlo_3489_, lean_object* v_hhi_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3484_, v_as_3485_, v_lo_3486_, v_hi_3487_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3492_, lean_object* v_as_3493_, lean_object* v_lo_3494_, lean_object* v_hi_3495_, lean_object* v_w_3496_, lean_object* v_hlo_3497_, lean_object* v_hhi_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3492_, v_as_3493_, v_lo_3494_, v_hi_3495_, v_w_3496_, v_hlo_3497_, v_hhi_3498_);
lean_dec(v_hi_3495_);
lean_dec(v_n_3492_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3500_, lean_object* v_lo_3501_, lean_object* v_hi_3502_, lean_object* v_hhi_3503_, lean_object* v_pivot_3504_, lean_object* v_as_3505_, lean_object* v_i_3506_, lean_object* v_k_3507_, lean_object* v_ilo_3508_, lean_object* v_ik_3509_, lean_object* v_w_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3502_, v_pivot_3504_, v_as_3505_, v_i_3506_, v_k_3507_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3512_, lean_object* v_lo_3513_, lean_object* v_hi_3514_, lean_object* v_hhi_3515_, lean_object* v_pivot_3516_, lean_object* v_as_3517_, lean_object* v_i_3518_, lean_object* v_k_3519_, lean_object* v_ilo_3520_, lean_object* v_ik_3521_, lean_object* v_w_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(v_n_3512_, v_lo_3513_, v_hi_3514_, v_hhi_3515_, v_pivot_3516_, v_as_3517_, v_i_3518_, v_k_3519_, v_ilo_3520_, v_ik_3521_, v_w_3522_);
lean_dec_ref(v_pivot_3516_);
lean_dec(v_hi_3514_);
lean_dec(v_lo_3513_);
lean_dec(v_n_3512_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3524_, lean_object* v_k_3525_, lean_object* v_x_3526_, lean_object* v_x_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_m_3530_; lean_object* v_a_3531_; uint8_t v___x_3532_; 
v___x_3528_ = lean_nat_add(v_x_3526_, v_x_3527_);
v___x_3529_ = lean_unsigned_to_nat(1u);
v_m_3530_ = lean_nat_shiftr(v___x_3528_, v___x_3529_);
lean_dec(v___x_3528_);
v_a_3531_ = lean_array_fget_borrowed(v_as_3524_, v_m_3530_);
v___x_3532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3531_, v_k_3525_);
if (v___x_3532_ == 0)
{
uint8_t v___x_3533_; 
lean_dec(v_x_3527_);
v___x_3533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3525_, v_a_3531_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_dec(v_m_3530_);
lean_dec(v_x_3526_);
lean_inc(v_a_3531_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_a_3531_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = lean_nat_dec_eq(v_m_3530_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3537_ = lean_nat_sub(v_m_3530_, v___x_3529_);
lean_dec(v_m_3530_);
v___x_3538_ = lean_nat_dec_lt(v___x_3537_, v_x_3526_);
if (v___x_3538_ == 0)
{
v_x_3527_ = v___x_3537_;
goto _start;
}
else
{
lean_object* v___x_3540_; 
lean_dec(v___x_3537_);
lean_dec(v_x_3526_);
v___x_3540_ = lean_box(0);
return v___x_3540_;
}
}
else
{
lean_object* v___x_3541_; 
lean_dec(v_m_3530_);
lean_dec(v_x_3526_);
v___x_3541_ = lean_box(0);
return v___x_3541_;
}
}
}
else
{
lean_object* v___x_3542_; uint8_t v___x_3543_; 
lean_dec(v_x_3526_);
v___x_3542_ = lean_nat_add(v_m_3530_, v___x_3529_);
lean_dec(v_m_3530_);
v___x_3543_ = lean_nat_dec_le(v___x_3542_, v_x_3527_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; 
lean_dec(v___x_3542_);
lean_dec(v_x_3527_);
v___x_3544_ = lean_box(0);
return v___x_3544_;
}
else
{
v_x_3526_ = v___x_3542_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3546_, lean_object* v_k_3547_, lean_object* v_x_3548_, lean_object* v_x_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3546_, v_k_3547_, v_x_3548_, v_x_3549_);
lean_dec_ref(v_k_3547_);
lean_dec_ref(v_as_3546_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3551_, lean_object* v_as_3552_, size_t v_sz_3553_, size_t v_i_3554_, lean_object* v_b_3555_){
_start:
{
lean_object* v_a_3557_; uint8_t v___x_3561_; 
v___x_3561_ = lean_usize_dec_lt(v_i_3554_, v_sz_3553_);
if (v___x_3561_ == 0)
{
lean_dec(v_tactic_3551_);
return v_b_3555_;
}
else
{
lean_object* v___x_3562_; lean_object* v_a_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3562_ = lean_unsigned_to_nat(0u);
v_a_3563_ = lean_array_uget_borrowed(v_as_3552_, v_i_3554_);
v___x_3564_ = lean_array_get_size(v_a_3563_);
v___x_3565_ = lean_nat_dec_lt(v___x_3562_, v___x_3564_);
if (v___x_3565_ == 0)
{
v_a_3557_ = v_b_3555_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_unsigned_to_nat(1u);
v___x_3567_ = lean_nat_sub(v___x_3564_, v___x_3566_);
v___x_3568_ = lean_nat_dec_le(v___x_3562_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_dec(v___x_3567_);
v_a_3557_ = v_b_3555_;
goto v___jp_3556_;
}
else
{
lean_object* v_extensions_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_extensions_3569_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3551_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_tactic_3551_);
lean_ctor_set(v___x_3570_, 1, v_extensions_3569_);
v___x_3571_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3563_, v___x_3570_, v___x_3562_, v___x_3567_);
lean_dec_ref_known(v___x_3570_, 2);
if (lean_obj_tag(v___x_3571_) == 1)
{
lean_object* v_val_3572_; lean_object* v_snd_3573_; lean_object* v___x_3574_; 
v_val_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v_snd_3573_ = lean_ctor_get(v_val_3572_, 1);
lean_inc(v_snd_3573_);
lean_dec(v_val_3572_);
v___x_3574_ = l_Array_append___redArg(v_b_3555_, v_snd_3573_);
lean_dec(v_snd_3573_);
v_a_3557_ = v___x_3574_;
goto v___jp_3556_;
}
else
{
lean_dec(v___x_3571_);
v_a_3557_ = v_b_3555_;
goto v___jp_3556_;
}
}
}
}
v___jp_3556_:
{
size_t v___x_3558_; size_t v___x_3559_; 
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3554_, v___x_3558_);
v_i_3554_ = v___x_3559_;
v_b_3555_ = v_a_3557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3575_, lean_object* v_as_3576_, lean_object* v_sz_3577_, lean_object* v_i_3578_, lean_object* v_b_3579_){
_start:
{
size_t v_sz_boxed_3580_; size_t v_i_boxed_3581_; lean_object* v_res_3582_; 
v_sz_boxed_3580_ = lean_unbox_usize(v_sz_3577_);
lean_dec(v_sz_3577_);
v_i_boxed_3581_ = lean_unbox_usize(v_i_3578_);
lean_dec(v_i_3578_);
v_res_3582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3575_, v_as_3576_, v_sz_boxed_3580_, v_i_boxed_3581_, v_b_3579_);
lean_dec_ref(v_as_3576_);
return v_res_3582_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = lean_box(1);
v___x_3584_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3585_, lean_object* v_tactic_3586_){
_start:
{
lean_object* v___x_3587_; lean_object* v_toEnvExtension_3588_; lean_object* v_asyncMode_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_importedEntries_3594_; lean_object* v_extensions_3595_; size_t v_sz_3596_; size_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3587_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3588_ = lean_ctor_get(v___x_3587_, 0);
v_asyncMode_3589_ = lean_ctor_get(v_toEnvExtension_3588_, 2);
v___x_3590_ = lean_box(1);
v___x_3591_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0, &l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0);
v___x_3592_ = lean_box(0);
lean_inc_ref(v_env_3585_);
v___x_3593_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3591_, v_toEnvExtension_3588_, v_env_3585_, v_asyncMode_3589_, v___x_3592_);
v_importedEntries_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_ref(v_importedEntries_3594_);
lean_dec(v___x_3593_);
v_extensions_3595_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3596_ = lean_array_size(v_importedEntries_3594_);
v___x_3597_ = ((size_t)0ULL);
lean_inc(v_tactic_3586_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3586_, v_importedEntries_3594_, v_sz_3596_, v___x_3597_, v_extensions_3595_);
lean_dec_ref(v_importedEntries_3594_);
v___x_3599_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3590_, v___x_3587_, v_env_3585_, v_asyncMode_3589_, v___x_3592_);
v___x_3600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3599_, v_tactic_3586_);
lean_dec(v_tactic_3586_);
lean_dec(v___x_3599_);
if (lean_obj_tag(v___x_3600_) == 1)
{
lean_object* v_val_3601_; lean_object* v___x_3602_; 
v_val_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_Array_append___redArg(v___x_3598_, v_val_3601_);
lean_dec(v_val_3601_);
return v___x_3602_;
}
else
{
lean_dec(v___x_3600_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3603_, lean_object* v_k_3604_, lean_object* v_x_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3603_, v_k_3604_, v_x_3605_, v_x_3606_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3609_, lean_object* v_k_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3609_, v_k_3610_, v_x_3611_, v_x_3612_, v_x_3613_);
lean_dec_ref(v_k_3610_);
lean_dec_ref(v_as_3609_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3615_, lean_object* v_pos_3616_){
_start:
{
lean_object* v_str_3617_; lean_object* v_startInclusive_3618_; lean_object* v_endExclusive_3619_; lean_object* v___x_3620_; uint8_t v___y_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; 
v_str_3617_ = lean_ctor_get(v_s_3615_, 0);
v_startInclusive_3618_ = lean_ctor_get(v_s_3615_, 1);
v_endExclusive_3619_ = lean_ctor_get(v_s_3615_, 2);
v___x_3620_ = lean_nat_add(v_startInclusive_3618_, v_pos_3616_);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_nat_sub(v_endExclusive_3619_, v___x_3620_);
v___x_3631_ = lean_nat_dec_eq(v___x_3629_, v___x_3630_);
lean_dec(v___x_3630_);
if (v___x_3631_ == 0)
{
uint32_t v___x_3632_; uint8_t v___y_3634_; uint32_t v___x_3639_; uint8_t v___x_3640_; 
v___x_3632_ = lean_string_utf8_get_fast(v_str_3617_, v___x_3620_);
v___x_3639_ = 32;
v___x_3640_ = lean_uint32_dec_eq(v___x_3632_, v___x_3639_);
if (v___x_3640_ == 0)
{
uint32_t v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = 9;
v___x_3642_ = lean_uint32_dec_eq(v___x_3632_, v___x_3641_);
v___y_3634_ = v___x_3642_;
goto v___jp_3633_;
}
else
{
v___y_3634_ = v___x_3640_;
goto v___jp_3633_;
}
v___jp_3633_:
{
if (v___y_3634_ == 0)
{
uint32_t v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = 13;
v___x_3636_ = lean_uint32_dec_eq(v___x_3632_, v___x_3635_);
if (v___x_3636_ == 0)
{
uint32_t v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = 10;
v___x_3638_ = lean_uint32_dec_eq(v___x_3632_, v___x_3637_);
v___y_3628_ = v___x_3638_;
goto v___jp_3627_;
}
else
{
v___y_3628_ = v___x_3636_;
goto v___jp_3627_;
}
}
else
{
goto v___jp_3621_;
}
}
}
else
{
lean_dec(v___x_3620_);
return v_pos_3616_;
}
v___jp_3621_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3622_ = lean_string_utf8_next_fast(v_str_3617_, v___x_3620_);
v___x_3623_ = lean_nat_sub(v___x_3622_, v___x_3620_);
lean_dec(v___x_3620_);
v___x_3624_ = lean_nat_add(v_pos_3616_, v___x_3623_);
lean_dec(v___x_3623_);
v___x_3625_ = lean_nat_dec_lt(v_pos_3616_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_dec(v___x_3624_);
return v_pos_3616_;
}
else
{
lean_dec(v_pos_3616_);
v_pos_3616_ = v___x_3624_;
goto _start;
}
}
v___jp_3627_:
{
if (v___y_3628_ == 0)
{
lean_dec(v___x_3620_);
return v_pos_3616_;
}
else
{
goto v___jp_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3643_, lean_object* v_pos_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3643_, v_pos_3644_);
lean_dec_ref(v_s_3643_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3648_){
_start:
{
lean_object* v___y_3650_; lean_object* v_str_3653_; lean_object* v_startInclusive_3654_; lean_object* v_endExclusive_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
v_str_3653_ = lean_ctor_get(v_str_3648_, 0);
v_startInclusive_3654_ = lean_ctor_get(v_str_3648_, 1);
v_endExclusive_3655_ = lean_ctor_get(v_str_3648_, 2);
v___x_3656_ = lean_unsigned_to_nat(0u);
v___x_3657_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3648_, v___x_3656_);
v___x_3658_ = lean_nat_sub(v_endExclusive_3655_, v_startInclusive_3654_);
v___x_3659_ = lean_nat_dec_eq(v___x_3657_, v___x_3658_);
lean_dec(v___x_3658_);
lean_dec(v___x_3657_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3661_ = lean_string_utf8_extract_fast(v_str_3653_, v_startInclusive_3654_, v_endExclusive_3655_);
v___x_3662_ = lean_string_append(v___x_3660_, v___x_3661_);
lean_dec_ref(v___x_3661_);
v___y_3650_ = v___x_3662_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_string_utf8_extract_fast(v_str_3653_, v_startInclusive_3654_, v_endExclusive_3655_);
v___y_3650_ = v___x_3663_;
goto v___jp_3649_;
}
v___jp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3652_ = lean_string_append(v___y_3650_, v___x_3651_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3664_);
lean_dec_ref(v_str_3664_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0));
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3670_);
lean_dec_ref(v_s_3670_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3672_, lean_object* v___x_3673_, lean_object* v___x_3674_, lean_object* v_a_3675_, lean_object* v_b_3676_){
_start:
{
lean_object* v_it_3678_; lean_object* v_startInclusive_3679_; lean_object* v_endExclusive_3680_; 
if (lean_obj_tag(v_a_3675_) == 0)
{
lean_object* v_currPos_3684_; lean_object* v_searcher_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3711_; 
v_currPos_3684_ = lean_ctor_get(v_a_3675_, 0);
v_searcher_3685_ = lean_ctor_get(v_a_3675_, 1);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_a_3675_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3687_ = v_a_3675_;
v_isShared_3688_ = v_isSharedCheck_3711_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_searcher_3685_);
lean_inc(v_currPos_3684_);
lean_dec(v_a_3675_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3711_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_startInclusive_3689_; lean_object* v_endExclusive_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v_startInclusive_3689_ = lean_ctor_get(v___x_3673_, 1);
v_endExclusive_3690_ = lean_ctor_get(v___x_3673_, 2);
v___x_3691_ = lean_nat_sub(v_endExclusive_3690_, v_startInclusive_3689_);
v___x_3692_ = lean_nat_dec_eq(v_searcher_3685_, v___x_3691_);
lean_dec(v___x_3691_);
if (v___x_3692_ == 0)
{
uint32_t v___x_3693_; uint32_t v___x_3694_; uint8_t v___x_3695_; 
v___x_3693_ = 10;
v___x_3694_ = lean_string_utf8_get_fast(v_str_3672_, v_searcher_3685_);
v___x_3695_ = lean_uint32_dec_eq(v___x_3694_, v___x_3693_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = lean_string_utf8_next_fast(v_str_3672_, v_searcher_3685_);
lean_dec(v_searcher_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v___x_3696_);
v___x_3698_ = v___x_3687_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_currPos_3684_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
v_a_3675_ = v___x_3698_;
goto _start;
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v_slice_3704_; lean_object* v_nextIt_3706_; 
v___x_3701_ = lean_string_utf8_next_fast(v_str_3672_, v_searcher_3685_);
v___x_3702_ = lean_nat_sub(v___x_3701_, v_searcher_3685_);
v___x_3703_ = lean_nat_add(v_searcher_3685_, v___x_3702_);
lean_dec(v___x_3702_);
v_slice_3704_ = l_String_Slice_subslice_x21(v___x_3673_, v_currPos_3684_, v_searcher_3685_);
lean_inc(v___x_3703_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v___x_3703_);
lean_ctor_set(v___x_3687_, 0, v___x_3703_);
v_nextIt_3706_ = v___x_3687_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3703_);
v_nextIt_3706_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v_startInclusive_3707_; lean_object* v_endExclusive_3708_; 
v_startInclusive_3707_ = lean_ctor_get(v_slice_3704_, 0);
lean_inc(v_startInclusive_3707_);
v_endExclusive_3708_ = lean_ctor_get(v_slice_3704_, 1);
lean_inc(v_endExclusive_3708_);
lean_dec_ref(v_slice_3704_);
v_it_3678_ = v_nextIt_3706_;
v_startInclusive_3679_ = v_startInclusive_3707_;
v_endExclusive_3680_ = v_endExclusive_3708_;
goto v___jp_3677_;
}
}
}
else
{
lean_object* v___x_3710_; 
lean_del_object(v___x_3687_);
lean_dec(v_searcher_3685_);
v___x_3710_ = lean_box(1);
lean_inc(v___x_3674_);
v_it_3678_ = v___x_3710_;
v_startInclusive_3679_ = v_currPos_3684_;
v_endExclusive_3680_ = v___x_3674_;
goto v___jp_3677_;
}
}
}
else
{
lean_dec(v___x_3674_);
lean_dec_ref(v_str_3672_);
return v_b_3676_;
}
v___jp_3677_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_inc_ref(v_str_3672_);
v___x_3681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3681_, 0, v_str_3672_);
lean_ctor_set(v___x_3681_, 1, v_startInclusive_3679_);
lean_ctor_set(v___x_3681_, 2, v_endExclusive_3680_);
v___x_3682_ = lean_array_push(v_b_3676_, v___x_3681_);
v_a_3675_ = v_it_3678_;
v_b_3676_ = v___x_3682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3712_, lean_object* v___x_3713_, lean_object* v___x_3714_, lean_object* v_a_3715_, lean_object* v_b_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3712_, v___x_3713_, v___x_3714_, v_a_3715_, v_b_3716_);
lean_dec_ref(v___x_3713_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3718_, lean_object* v_x_3719_){
_start:
{
if (lean_obj_tag(v_x_3719_) == 0)
{
return v_x_3718_;
}
else
{
lean_object* v_head_3720_; lean_object* v_tail_3721_; lean_object* v___x_3722_; 
v_head_3720_ = lean_ctor_get(v_x_3719_, 0);
v_tail_3721_ = lean_ctor_get(v_x_3719_, 1);
v___x_3722_ = lean_string_append(v_x_3718_, v_head_3720_);
v_x_3718_ = v___x_3722_;
v_x_3719_ = v_tail_3721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3724_, lean_object* v_x_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3724_, v_x_3725_);
lean_dec(v_x_3725_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
if (lean_obj_tag(v_a_3727_) == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = l_List_reverse___redArg(v_a_3728_);
return v___x_3729_;
}
else
{
lean_object* v_head_3730_; lean_object* v_tail_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
v_head_3730_ = lean_ctor_get(v_a_3727_, 0);
v_tail_3731_ = lean_ctor_get(v_a_3727_, 1);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3733_ = v_a_3727_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_tail_3731_);
lean_inc(v_head_3730_);
lean_dec(v_a_3727_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3730_);
lean_dec(v_head_3730_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v_a_3728_);
lean_ctor_set(v___x_3733_, 0, v___x_3735_);
v___x_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_a_3728_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
v_a_3727_ = v_tail_3731_;
v_a_3728_ = v___x_3737_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3745_){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v_lines_3752_; 
v___x_3746_ = lean_unsigned_to_nat(0u);
v___x_3747_ = lean_string_utf8_byte_size(v_str_3745_);
lean_inc_ref(v_str_3745_);
v___x_3748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3748_, 0, v_str_3745_);
lean_ctor_set(v___x_3748_, 1, v___x_3746_);
lean_ctor_set(v___x_3748_, 2, v___x_3747_);
v___x_3749_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v___x_3748_);
v___x_3750_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3751_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3745_, v___x_3748_, v___x_3747_, v___x_3749_, v___x_3750_);
lean_dec_ref_known(v___x_3748_, 3);
v_lines_3752_ = lean_array_to_list(v___x_3751_);
if (lean_obj_tag(v_lines_3752_) == 0)
{
lean_object* v___x_3753_; 
v___x_3753_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3753_;
}
else
{
lean_object* v_tail_3754_; 
v_tail_3754_ = lean_ctor_get(v_lines_3752_, 1);
lean_inc(v_tail_3754_);
if (lean_obj_tag(v_tail_3754_) == 0)
{
lean_object* v_head_3755_; lean_object* v_str_3756_; lean_object* v_startInclusive_3757_; lean_object* v_endExclusive_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_head_3755_ = lean_ctor_get(v_lines_3752_, 0);
lean_inc(v_head_3755_);
lean_dec_ref_known(v_lines_3752_, 2);
v_str_3756_ = lean_ctor_get(v_head_3755_, 0);
lean_inc_ref(v_str_3756_);
v_startInclusive_3757_ = lean_ctor_get(v_head_3755_, 1);
lean_inc(v_startInclusive_3757_);
v_endExclusive_3758_ = lean_ctor_get(v_head_3755_, 2);
lean_inc(v_endExclusive_3758_);
lean_dec(v_head_3755_);
v___x_3759_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3760_ = lean_string_utf8_extract_fast(v_str_3756_, v_startInclusive_3757_, v_endExclusive_3758_);
lean_dec(v_endExclusive_3758_);
lean_dec(v_startInclusive_3757_);
lean_dec_ref(v_str_3756_);
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
return v___x_3763_;
}
else
{
lean_object* v_head_3764_; lean_object* v_str_3765_; lean_object* v_startInclusive_3766_; lean_object* v_endExclusive_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_head_3764_ = lean_ctor_get(v_lines_3752_, 0);
lean_inc(v_head_3764_);
lean_dec_ref_known(v_lines_3752_, 2);
v_str_3765_ = lean_ctor_get(v_head_3764_, 0);
lean_inc_ref(v_str_3765_);
v_startInclusive_3766_ = lean_ctor_get(v_head_3764_, 1);
lean_inc(v_startInclusive_3766_);
v_endExclusive_3767_ = lean_ctor_get(v_head_3764_, 2);
lean_inc(v_endExclusive_3767_);
lean_dec(v_head_3764_);
v___x_3768_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3769_ = lean_string_utf8_extract_fast(v_str_3765_, v_startInclusive_3766_, v_endExclusive_3767_);
lean_dec(v_endExclusive_3767_);
lean_dec(v_startInclusive_3766_);
lean_dec_ref(v_str_3765_);
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3772_ = lean_string_append(v___x_3770_, v___x_3771_);
v___x_3773_ = lean_box(0);
v___x_3774_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3754_, v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3776_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3775_, v___x_3774_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_string_append(v___x_3772_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3779_ = lean_string_append(v___x_3777_, v___x_3778_);
return v___x_3779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3780_, lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v_inst_3783_, lean_object* v_R_3784_, lean_object* v_a_3785_, lean_object* v_b_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3780_, v___x_3781_, v___x_3782_, v_a_3785_, v_b_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3788_, lean_object* v___x_3789_, lean_object* v___x_3790_, lean_object* v_inst_3791_, lean_object* v_R_3792_, lean_object* v_a_3793_, lean_object* v_b_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3788_, v___x_3789_, v___x_3790_, v_inst_3791_, v_R_3792_, v_a_3793_, v_b_3794_);
lean_dec_ref(v___x_3789_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
if (lean_obj_tag(v_a_3796_) == 0)
{
lean_object* v___x_3798_; 
v___x_3798_ = l_List_reverse___redArg(v_a_3797_);
return v___x_3798_;
}
else
{
lean_object* v_head_3799_; lean_object* v_tail_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3809_; 
v_head_3799_ = lean_ctor_get(v_a_3796_, 0);
v_tail_3800_ = lean_ctor_get(v_a_3796_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_a_3796_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3802_ = v_a_3796_;
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_tail_3800_);
lean_inc(v_head_3799_);
lean_dec(v_a_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3799_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 1, v_a_3797_);
lean_ctor_set(v___x_3802_, 0, v___x_3804_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_a_3797_);
v___x_3806_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v_a_3796_ = v_tail_3800_;
v_a_3797_ = v___x_3806_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3810_, lean_object* v_pos_3811_){
_start:
{
lean_object* v_str_3812_; lean_object* v_startInclusive_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_str_3812_ = lean_ctor_get(v_s_3810_, 0);
v_startInclusive_3813_ = lean_ctor_get(v_s_3810_, 1);
v___x_3814_ = lean_nat_add(v_startInclusive_3813_, v_pos_3811_);
v___x_3815_ = lean_nat_sub(v___x_3814_, v_startInclusive_3813_);
v___x_3816_ = lean_unsigned_to_nat(0u);
v___x_3817_ = lean_nat_dec_eq(v___x_3815_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___y_3826_; lean_object* v___x_3827_; uint32_t v___x_3828_; uint8_t v___y_3830_; uint32_t v___x_3835_; uint8_t v___x_3836_; 
lean_inc(v_startInclusive_3813_);
lean_inc_ref(v_str_3812_);
v___x_3818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3818_, 0, v_str_3812_);
lean_ctor_set(v___x_3818_, 1, v_startInclusive_3813_);
lean_ctor_set(v___x_3818_, 2, v___x_3814_);
v___x_3819_ = lean_unsigned_to_nat(1u);
v___x_3820_ = lean_nat_sub(v___x_3815_, v___x_3819_);
lean_dec(v___x_3815_);
v___x_3821_ = l_String_Slice_posLE(v___x_3818_, v___x_3820_);
lean_dec_ref_known(v___x_3818_, 3);
v___x_3827_ = lean_nat_add(v_startInclusive_3813_, v___x_3821_);
v___x_3828_ = lean_string_utf8_get_fast(v_str_3812_, v___x_3827_);
lean_dec(v___x_3827_);
v___x_3835_ = 32;
v___x_3836_ = lean_uint32_dec_eq(v___x_3828_, v___x_3835_);
if (v___x_3836_ == 0)
{
uint32_t v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = 9;
v___x_3838_ = lean_uint32_dec_eq(v___x_3828_, v___x_3837_);
v___y_3830_ = v___x_3838_;
goto v___jp_3829_;
}
else
{
v___y_3830_ = v___x_3836_;
goto v___jp_3829_;
}
v___jp_3822_:
{
uint8_t v___x_3823_; 
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v_pos_3811_);
if (v___x_3823_ == 0)
{
lean_dec(v___x_3821_);
return v_pos_3811_;
}
else
{
lean_dec(v_pos_3811_);
v_pos_3811_ = v___x_3821_;
goto _start;
}
}
v___jp_3825_:
{
if (v___y_3826_ == 0)
{
lean_dec(v___x_3821_);
return v_pos_3811_;
}
else
{
goto v___jp_3822_;
}
}
v___jp_3829_:
{
if (v___y_3830_ == 0)
{
uint32_t v___x_3831_; uint8_t v___x_3832_; 
v___x_3831_ = 13;
v___x_3832_ = lean_uint32_dec_eq(v___x_3828_, v___x_3831_);
if (v___x_3832_ == 0)
{
uint32_t v___x_3833_; uint8_t v___x_3834_; 
v___x_3833_ = 10;
v___x_3834_ = lean_uint32_dec_eq(v___x_3828_, v___x_3833_);
v___y_3826_ = v___x_3834_;
goto v___jp_3825_;
}
else
{
v___y_3826_ = v___x_3832_;
goto v___jp_3825_;
}
}
else
{
goto v___jp_3822_;
}
}
}
else
{
lean_dec(v___x_3815_);
lean_dec(v___x_3814_);
return v_pos_3811_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3839_, lean_object* v_pos_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3839_, v_pos_3840_);
lean_dec_ref(v_s_3839_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3843_, lean_object* v_tactic_3844_){
_start:
{
lean_object* v_exts_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_exts_3845_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3843_, v_tactic_3844_);
v___x_3846_ = lean_array_get_size(v_exts_3845_);
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = lean_nat_dec_eq(v___x_3846_, v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3849_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3850_ = lean_array_to_list(v_exts_3845_);
v___x_3851_ = lean_box(0);
v___x_3852_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3850_, v___x_3851_);
v___x_3853_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3854_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3853_, v___x_3852_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_string_append(v___x_3849_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = lean_string_utf8_byte_size(v___x_3855_);
lean_inc_ref(v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3847_);
lean_ctor_set(v___x_3857_, 2, v___x_3856_);
v___x_3858_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3857_, v___x_3856_);
lean_dec_ref_known(v___x_3857_, 3);
v___x_3859_ = lean_string_utf8_extract_fast(v___x_3855_, v___x_3847_, v___x_3858_);
lean_dec(v___x_3858_);
lean_dec_ref(v___x_3855_);
return v___x_3859_;
}
else
{
lean_object* v___x_3860_; 
lean_dec_ref(v_exts_3845_);
v___x_3860_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3861_, lean_object* v_x_3862_){
_start:
{
lean_object* v_fst_3863_; lean_object* v_snd_3864_; lean_object* v___x_3865_; 
v_fst_3863_ = lean_ctor_get(v_x_3862_, 0);
lean_inc(v_fst_3863_);
v_snd_3864_ = lean_ctor_get(v_x_3862_, 1);
lean_inc(v_snd_3864_);
lean_dec_ref(v_x_3862_);
v___x_3865_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3863_, v_snd_3864_, v_as_3861_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3866_, lean_object* v_x_3867_){
_start:
{
if (lean_obj_tag(v_x_3867_) == 0)
{
lean_object* v_k_3868_; lean_object* v_v_3869_; lean_object* v_l_3870_; lean_object* v_r_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_k_3868_ = lean_ctor_get(v_x_3867_, 1);
v_v_3869_ = lean_ctor_get(v_x_3867_, 2);
v_l_3870_ = lean_ctor_get(v_x_3867_, 3);
v_r_3871_ = lean_ctor_get(v_x_3867_, 4);
v___x_3872_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3866_, v_l_3870_);
lean_inc(v_v_3869_);
lean_inc(v_k_3868_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v_k_3868_);
lean_ctor_set(v___x_3873_, 1, v_v_3869_);
v___x_3874_ = lean_array_push(v___x_3872_, v___x_3873_);
v_init_3866_ = v___x_3874_;
v_x_3867_ = v_r_3871_;
goto _start;
}
else
{
return v_init_3866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3876_, lean_object* v_x_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3876_, v_x_3877_);
lean_dec(v_x_3877_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3879_, lean_object* v_pivot_3880_, lean_object* v_as_3881_, lean_object* v_i_3882_, lean_object* v_k_3883_){
_start:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_nat_dec_lt(v_k_3883_, v_hi_3879_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec(v_k_3883_);
v___x_3885_ = lean_array_fswap(v_as_3881_, v_i_3882_, v_hi_3879_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v_i_3882_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
return v___x_3886_;
}
else
{
lean_object* v___x_3887_; lean_object* v_fst_3888_; lean_object* v_fst_3889_; uint8_t v___x_3890_; 
v___x_3887_ = lean_array_fget_borrowed(v_as_3881_, v_k_3883_);
v_fst_3888_ = lean_ctor_get(v___x_3887_, 0);
v_fst_3889_ = lean_ctor_get(v_pivot_3880_, 0);
v___x_3890_ = l_Lean_Name_quickLt(v_fst_3888_, v_fst_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_nat_add(v_k_3883_, v___x_3891_);
lean_dec(v_k_3883_);
v_k_3883_ = v___x_3892_;
goto _start;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = lean_array_fswap(v_as_3881_, v_i_3882_, v_k_3883_);
v___x_3895_ = lean_unsigned_to_nat(1u);
v___x_3896_ = lean_nat_add(v_i_3882_, v___x_3895_);
lean_dec(v_i_3882_);
v___x_3897_ = lean_nat_add(v_k_3883_, v___x_3895_);
lean_dec(v_k_3883_);
v_as_3881_ = v___x_3894_;
v_i_3882_ = v___x_3896_;
v_k_3883_ = v___x_3897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3899_, lean_object* v_pivot_3900_, lean_object* v_as_3901_, lean_object* v_i_3902_, lean_object* v_k_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3899_, v_pivot_3900_, v_as_3901_, v_i_3902_, v_k_3903_);
lean_dec_ref(v_pivot_3900_);
lean_dec(v_hi_3899_);
return v_res_3904_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3905_, lean_object* v_x2_3906_){
_start:
{
lean_object* v_fst_3907_; lean_object* v_fst_3908_; uint8_t v___x_3909_; 
v_fst_3907_ = lean_ctor_get(v_x1_3905_, 0);
v_fst_3908_ = lean_ctor_get(v_x2_3906_, 0);
v___x_3909_ = l_Lean_Name_quickLt(v_fst_3907_, v_fst_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3910_, lean_object* v_x2_3911_){
_start:
{
uint8_t v_res_3912_; lean_object* v_r_3913_; 
v_res_3912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3910_, v_x2_3911_);
lean_dec_ref(v_x2_3911_);
lean_dec_ref(v_x1_3910_);
v_r_3913_ = lean_box(v_res_3912_);
return v_r_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3914_, lean_object* v_as_3915_, lean_object* v_lo_3916_, lean_object* v_hi_3917_){
_start:
{
lean_object* v___y_3919_; uint8_t v___x_3929_; 
v___x_3929_ = lean_nat_dec_lt(v_lo_3916_, v_hi_3917_);
if (v___x_3929_ == 0)
{
lean_dec(v_lo_3916_);
return v_as_3915_;
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_mid_3932_; lean_object* v___y_3934_; lean_object* v___y_3940_; lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3930_ = lean_nat_add(v_lo_3916_, v_hi_3917_);
v___x_3931_ = lean_unsigned_to_nat(1u);
v_mid_3932_ = lean_nat_shiftr(v___x_3930_, v___x_3931_);
lean_dec(v___x_3930_);
v___x_3945_ = lean_array_fget_borrowed(v_as_3915_, v_mid_3932_);
v___x_3946_ = lean_array_fget_borrowed(v_as_3915_, v_lo_3916_);
v___x_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3945_, v___x_3946_);
if (v___x_3947_ == 0)
{
v___y_3940_ = v_as_3915_;
goto v___jp_3939_;
}
else
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_array_fswap(v_as_3915_, v_lo_3916_, v_mid_3932_);
v___y_3940_ = v___x_3948_;
goto v___jp_3939_;
}
v___jp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v___x_3935_ = lean_array_fget_borrowed(v___y_3934_, v_mid_3932_);
v___x_3936_ = lean_array_fget_borrowed(v___y_3934_, v_hi_3917_);
v___x_3937_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_dec(v_mid_3932_);
v___y_3919_ = v___y_3934_;
goto v___jp_3918_;
}
else
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_array_fswap(v___y_3934_, v_mid_3932_, v_hi_3917_);
lean_dec(v_mid_3932_);
v___y_3919_ = v___x_3938_;
goto v___jp_3918_;
}
}
v___jp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = lean_array_fget_borrowed(v___y_3940_, v_hi_3917_);
v___x_3942_ = lean_array_fget_borrowed(v___y_3940_, v_lo_3916_);
v___x_3943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
v___y_3934_ = v___y_3940_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_array_fswap(v___y_3940_, v_lo_3916_, v_hi_3917_);
v___y_3934_ = v___x_3944_;
goto v___jp_3933_;
}
}
}
v___jp_3918_:
{
lean_object* v_pivot_3920_; lean_object* v___x_3921_; lean_object* v_fst_3922_; lean_object* v_snd_3923_; uint8_t v___x_3924_; 
v_pivot_3920_ = lean_array_fget(v___y_3919_, v_hi_3917_);
lean_inc_n(v_lo_3916_, 2);
v___x_3921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3917_, v_pivot_3920_, v___y_3919_, v_lo_3916_, v_lo_3916_);
lean_dec(v_pivot_3920_);
v_fst_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_fst_3922_);
v_snd_3923_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_snd_3923_);
lean_dec_ref(v___x_3921_);
v___x_3924_ = lean_nat_dec_le(v_hi_3917_, v_fst_3922_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3914_, v_snd_3923_, v_lo_3916_, v_fst_3922_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_add(v_fst_3922_, v___x_3926_);
lean_dec(v_fst_3922_);
v_as_3915_ = v___x_3925_;
v_lo_3916_ = v___x_3927_;
goto _start;
}
else
{
lean_dec(v_fst_3922_);
lean_dec(v_lo_3916_);
return v_snd_3923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3949_, lean_object* v_as_3950_, lean_object* v_lo_3951_, lean_object* v_hi_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3949_, v_as_3950_, v_lo_3951_, v_hi_3952_);
lean_dec(v_hi_3952_);
lean_dec(v_n_3949_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3956_, lean_object* v_s_3957_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___y_3963_; lean_object* v___y_3964_; uint8_t v___x_3967_; 
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3960_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3959_, v_s_3957_);
v___x_3961_ = lean_array_get_size(v___x_3960_);
v___x_3967_ = lean_nat_dec_eq(v___x_3961_, v___x_3958_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___y_3971_; uint8_t v___x_3973_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_sub(v___x_3961_, v___x_3968_);
v___x_3973_ = lean_nat_dec_le(v___x_3958_, v___x_3969_);
if (v___x_3973_ == 0)
{
lean_inc(v___x_3969_);
v___y_3971_ = v___x_3969_;
goto v___jp_3970_;
}
else
{
v___y_3971_ = v___x_3958_;
goto v___jp_3970_;
}
v___jp_3970_:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_le(v___y_3971_, v___x_3969_);
if (v___x_3972_ == 0)
{
lean_dec(v___x_3969_);
lean_inc(v___y_3971_);
v___y_3963_ = v___y_3971_;
v___y_3964_ = v___y_3971_;
goto v___jp_3962_;
}
else
{
v___y_3963_ = v___y_3971_;
v___y_3964_ = v___x_3969_;
goto v___jp_3962_;
}
}
}
else
{
lean_object* v___x_3974_; 
lean_inc_ref_n(v___x_3960_, 2);
v___x_3974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3960_);
lean_ctor_set(v___x_3974_, 1, v___x_3960_);
lean_ctor_set(v___x_3974_, 2, v___x_3960_);
return v___x_3974_;
}
v___jp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3961_, v___x_3960_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
lean_inc_ref_n(v___x_3965_, 2);
v___x_3966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
lean_ctor_set(v___x_3966_, 2, v___x_3965_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3975_, lean_object* v_s_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3975_, v_s_3976_);
lean_dec(v_s_3976_);
lean_dec_ref(v_x_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3978_){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v___x_3980_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3981_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3980_, v_es_3978_);
v___x_3982_ = lean_array_get_size(v___x_3981_);
v___x_3983_ = lean_nat_dec_eq(v___x_3982_, v___x_3979_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___y_3987_; uint8_t v___x_3991_; 
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = lean_nat_sub(v___x_3982_, v___x_3984_);
v___x_3991_ = lean_nat_dec_le(v___x_3979_, v___x_3985_);
if (v___x_3991_ == 0)
{
lean_inc(v___x_3985_);
v___y_3987_ = v___x_3985_;
goto v___jp_3986_;
}
else
{
v___y_3987_ = v___x_3979_;
goto v___jp_3986_;
}
v___jp_3986_:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_le(v___y_3987_, v___x_3985_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v___x_3985_);
lean_inc(v___y_3987_);
v___x_3989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3982_, v___x_3981_, v___y_3987_, v___y_3987_);
lean_dec(v___y_3987_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; 
v___x_3990_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3982_, v___x_3981_, v___y_3987_, v___x_3985_);
lean_dec(v___x_3985_);
return v___x_3990_;
}
}
}
else
{
return v___x_3981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_3992_);
lean_dec(v_es_3992_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_3994_, lean_object* v_x_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3994_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_3999_, lean_object* v_x_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_3999_, v_x_4000_, v___y_4001_);
lean_dec_ref(v___y_4001_);
lean_dec_ref(v_x_4000_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_4030_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_4033_, lean_object* v_t_4034_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_4033_, v_t_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4036_, lean_object* v_t_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_4036_, v_t_4037_);
lean_dec(v_t_4037_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_4039_, lean_object* v_as_4040_, lean_object* v_lo_4041_, lean_object* v_hi_4042_, lean_object* v_w_4043_, lean_object* v_hlo_4044_, lean_object* v_hhi_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_4039_, v_as_4040_, v_lo_4041_, v_hi_4042_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_4047_, lean_object* v_as_4048_, lean_object* v_lo_4049_, lean_object* v_hi_4050_, lean_object* v_w_4051_, lean_object* v_hlo_4052_, lean_object* v_hhi_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_4047_, v_as_4048_, v_lo_4049_, v_hi_4050_, v_w_4051_, v_hlo_4052_, v_hhi_4053_);
lean_dec(v_hi_4050_);
lean_dec(v_n_4047_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_4055_, lean_object* v_lo_4056_, lean_object* v_hi_4057_, lean_object* v_hhi_4058_, lean_object* v_pivot_4059_, lean_object* v_as_4060_, lean_object* v_i_4061_, lean_object* v_k_4062_, lean_object* v_ilo_4063_, lean_object* v_ik_4064_, lean_object* v_w_4065_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_4057_, v_pivot_4059_, v_as_4060_, v_i_4061_, v_k_4062_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_4067_, lean_object* v_lo_4068_, lean_object* v_hi_4069_, lean_object* v_hhi_4070_, lean_object* v_pivot_4071_, lean_object* v_as_4072_, lean_object* v_i_4073_, lean_object* v_k_4074_, lean_object* v_ilo_4075_, lean_object* v_ik_4076_, lean_object* v_w_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(v_n_4067_, v_lo_4068_, v_hi_4069_, v_hhi_4070_, v_pivot_4071_, v_as_4072_, v_i_4073_, v_k_4074_, v_ilo_4075_, v_ik_4076_, v_w_4077_);
lean_dec_ref(v_pivot_4071_);
lean_dec(v_hi_4069_);
lean_dec(v_lo_4068_);
lean_dec(v_n_4067_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_4080_, lean_object* v___x_4081_, lean_object* v_toPure_4082_, lean_object* v___f_4083_, lean_object* v_env_4084_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4084_, v_tac_4080_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v___x_4089_; lean_object* v_toEnvExtension_4090_; lean_object* v_asyncMode_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec_ref(v___f_4083_);
v___x_4089_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4090_ = lean_ctor_get(v___x_4089_, 0);
v_asyncMode_4091_ = lean_ctor_get(v_toEnvExtension_4090_, 2);
v___x_4092_ = lean_box(0);
v___x_4093_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4081_, v___x_4089_, v_env_4084_, v_asyncMode_4091_, v___x_4092_);
v___x_4094_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4093_, v_tac_4080_);
lean_dec(v_tac_4080_);
lean_dec(v___x_4093_);
v___x_4095_ = lean_apply_2(v_toPure_4082_, lean_box(0), v___x_4094_);
return v___x_4095_;
}
else
{
lean_object* v_val_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; 
v_val_4096_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v___x_4088_, 1);
v___x_4097_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4098_ = 0;
v___x_4099_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4081_, v___x_4097_, v_env_4084_, v_val_4096_, v___x_4098_);
lean_dec(v_val_4096_);
lean_dec_ref(v_env_4084_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = lean_array_get_size(v___x_4099_);
v___x_4102_ = lean_nat_dec_lt(v___x_4100_, v___x_4101_);
if (v___x_4102_ == 0)
{
lean_dec_ref(v___x_4099_);
lean_dec_ref(v___f_4083_);
lean_dec(v_tac_4080_);
goto v___jp_4085_;
}
else
{
lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v___x_4103_ = lean_unsigned_to_nat(1u);
v___x_4104_ = lean_nat_sub(v___x_4101_, v___x_4103_);
v___x_4105_ = lean_nat_dec_le(v___x_4100_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_dec(v___x_4104_);
lean_dec_ref(v___x_4099_);
lean_dec_ref(v___f_4083_);
lean_dec(v_tac_4080_);
goto v___jp_4085_;
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4106_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v_tac_4080_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_4109_ = l_Array_binSearchAux___redArg(v___f_4083_, v___x_4108_, v___x_4099_, v___x_4107_, v___x_4100_, v___x_4104_);
lean_dec_ref(v___x_4099_);
if (lean_obj_tag(v___x_4109_) == 0)
{
goto v___jp_4085_;
}
else
{
lean_object* v_val_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4119_; 
v_val_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4119_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_val_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4119_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_snd_4114_; lean_object* v___x_4116_; 
v_snd_4114_ = lean_ctor_get(v_val_4110_, 1);
lean_inc(v_snd_4114_);
lean_dec(v_val_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v_snd_4114_);
v___x_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_snd_4114_);
v___x_4116_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_apply_2(v_toPure_4082_, lean_box(0), v___x_4116_);
return v___x_4117_;
}
}
}
}
}
}
v___jp_4085_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_box(0);
v___x_4087_ = lean_apply_2(v_toPure_4082_, lean_box(0), v___x_4086_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_4121_, lean_object* v_inst_4122_, lean_object* v_tac_4123_){
_start:
{
lean_object* v_toApplicative_4124_; lean_object* v_toBind_4125_; lean_object* v_getEnv_4126_; lean_object* v_toPure_4127_; lean_object* v___f_4128_; lean_object* v___x_4129_; lean_object* v___f_4130_; lean_object* v___x_4131_; 
v_toApplicative_4124_ = lean_ctor_get(v_inst_4121_, 0);
lean_inc_ref(v_toApplicative_4124_);
v_toBind_4125_ = lean_ctor_get(v_inst_4121_, 1);
lean_inc(v_toBind_4125_);
lean_dec_ref(v_inst_4121_);
v_getEnv_4126_ = lean_ctor_get(v_inst_4122_, 0);
lean_inc(v_getEnv_4126_);
lean_dec_ref(v_inst_4122_);
v_toPure_4127_ = lean_ctor_get(v_toApplicative_4124_, 1);
lean_inc(v_toPure_4127_);
lean_dec_ref(v_toApplicative_4124_);
v___f_4128_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0));
v___x_4129_ = lean_box(1);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4130_, 0, v_tac_4123_);
lean_closure_set(v___f_4130_, 1, v___x_4129_);
lean_closure_set(v___f_4130_, 2, v_toPure_4127_);
lean_closure_set(v___f_4130_, 3, v___f_4128_);
v___x_4131_ = lean_apply_4(v_toBind_4125_, lean_box(0), lean_box(0), v_getEnv_4126_, v___f_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_4132_, lean_object* v_inst_4133_, lean_object* v_inst_4134_, lean_object* v_tac_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_4133_, v_inst_4134_, v_tac_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4137_, lean_object* v_k_4138_, lean_object* v_x_4139_, lean_object* v_x_4140_){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v_m_4143_; lean_object* v_a_4144_; uint8_t v___x_4145_; 
v___x_4141_ = lean_nat_add(v_x_4139_, v_x_4140_);
v___x_4142_ = lean_unsigned_to_nat(1u);
v_m_4143_ = lean_nat_shiftr(v___x_4141_, v___x_4142_);
lean_dec(v___x_4141_);
v_a_4144_ = lean_array_fget_borrowed(v_as_4137_, v_m_4143_);
v___x_4145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_4144_, v_k_4138_);
if (v___x_4145_ == 0)
{
uint8_t v___x_4146_; 
lean_dec(v_x_4140_);
v___x_4146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_4138_, v_a_4144_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_dec(v_m_4143_);
lean_dec(v_x_4139_);
lean_inc(v_a_4144_);
v___x_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_a_4144_);
return v___x_4147_;
}
else
{
lean_object* v___x_4148_; uint8_t v___x_4149_; 
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = lean_nat_dec_eq(v_m_4143_, v___x_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = lean_nat_sub(v_m_4143_, v___x_4142_);
lean_dec(v_m_4143_);
v___x_4151_ = lean_nat_dec_lt(v___x_4150_, v_x_4139_);
if (v___x_4151_ == 0)
{
v_x_4140_ = v___x_4150_;
goto _start;
}
else
{
lean_object* v___x_4153_; 
lean_dec(v___x_4150_);
lean_dec(v_x_4139_);
v___x_4153_ = lean_box(0);
return v___x_4153_;
}
}
else
{
lean_object* v___x_4154_; 
lean_dec(v_m_4143_);
lean_dec(v_x_4139_);
v___x_4154_ = lean_box(0);
return v___x_4154_;
}
}
}
else
{
lean_object* v___x_4155_; uint8_t v___x_4156_; 
lean_dec(v_x_4139_);
v___x_4155_ = lean_nat_add(v_m_4143_, v___x_4142_);
lean_dec(v_m_4143_);
v___x_4156_ = lean_nat_dec_le(v___x_4155_, v_x_4140_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
lean_dec(v___x_4155_);
lean_dec(v_x_4140_);
v___x_4157_ = lean_box(0);
return v___x_4157_;
}
else
{
v_x_4139_ = v___x_4155_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4159_, lean_object* v_k_4160_, lean_object* v_x_4161_, lean_object* v_x_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4159_, v_k_4160_, v_x_4161_, v_x_4162_);
lean_dec_ref(v_k_4160_);
lean_dec_ref(v_as_4159_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v___x_4167_; lean_object* v_env_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4167_ = lean_st_ref_get(v___y_4165_);
v_env_4171_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_ref(v_env_4171_);
lean_dec(v___x_4167_);
v___x_4172_ = lean_box(1);
v___x_4173_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4171_, v_tac_4164_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v___x_4174_; lean_object* v_toEnvExtension_4175_; lean_object* v_asyncMode_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4174_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4175_ = lean_ctor_get(v___x_4174_, 0);
v_asyncMode_4176_ = lean_ctor_get(v_toEnvExtension_4175_, 2);
v___x_4177_ = lean_box(0);
v___x_4178_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4172_, v___x_4174_, v_env_4171_, v_asyncMode_4176_, v___x_4177_);
v___x_4179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4178_, v_tac_4164_);
lean_dec(v_tac_4164_);
lean_dec(v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
else
{
lean_object* v_val_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4209_; 
v_val_4181_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4183_ = v___x_4173_;
v_isShared_4184_ = v_isSharedCheck_4209_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_val_4181_);
lean_dec(v___x_4173_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4209_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4185_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4186_ = 0;
v___x_4187_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4172_, v___x_4185_, v_env_4171_, v_val_4181_, v___x_4186_);
lean_dec(v_val_4181_);
lean_dec_ref(v_env_4171_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_array_get_size(v___x_4187_);
v___x_4190_ = lean_nat_dec_lt(v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_dec_ref(v___x_4187_);
lean_del_object(v___x_4183_);
lean_dec(v_tac_4164_);
goto v___jp_4168_;
}
else
{
lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_sub(v___x_4189_, v___x_4191_);
v___x_4193_ = lean_nat_dec_le(v___x_4188_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_dec(v___x_4192_);
lean_dec_ref(v___x_4187_);
lean_del_object(v___x_4183_);
lean_dec(v_tac_4164_);
goto v___jp_4168_;
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v_tac_4164_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4187_, v___x_4195_, v___x_4188_, v___x_4192_);
lean_dec_ref_known(v___x_4195_, 2);
lean_dec_ref(v___x_4187_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_del_object(v___x_4183_);
goto v___jp_4168_;
}
else
{
lean_object* v_val_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4208_; 
v_val_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4208_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_val_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4208_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_snd_4201_; lean_object* v___x_4203_; 
v_snd_4201_ = lean_ctor_get(v_val_4197_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_val_4197_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_snd_4201_);
v___x_4203_ = v___x_4199_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_snd_4201_);
v___x_4203_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4205_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set_tag(v___x_4183_, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4203_);
v___x_4205_ = v___x_4183_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
}
}
}
v___jp_4168_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_box(0);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4210_, v___y_4211_);
lean_dec(v___y_4211_);
return v_res_4213_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4216_ = l_Lean_stringToMessageData(v___x_4215_);
return v___x_4216_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4218_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4219_ = l_Lean_stringToMessageData(v___x_4218_);
return v___x_4219_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4222_ = l_Lean_stringToMessageData(v___x_4221_);
return v___x_4222_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4224_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4225_ = l_Lean_stringToMessageData(v___x_4224_);
return v___x_4225_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4228_ = l_Lean_stringToMessageData(v___x_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_4235_, lean_object* v___x_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v_name_4239_, lean_object* v_decl_4240_, lean_object* v_stx_4241_, uint8_t v_kind_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4312_; uint8_t v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v_name_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; uint8_t v___x_4400_; uint8_t v___x_4401_; 
v___x_4400_ = 0;
v___x_4401_ = l_Lean_instBEqAttributeKind_beq(v_kind_4242_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; 
lean_dec(v_stx_4241_);
lean_dec(v_decl_4240_);
lean_dec_ref(v___x_4238_);
lean_dec_ref(v___x_4237_);
lean_dec_ref(v___x_4236_);
lean_dec(v___x_4235_);
v___x_4402_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_4239_, v_kind_4242_, v___y_4243_, v___y_4244_);
return v___x_4402_;
}
else
{
goto v___jp_4359_;
}
v___jp_4246_:
{
lean_object* v___x_4249_; lean_object* v_env_4250_; lean_object* v_nextMacroScope_4251_; lean_object* v_ngen_4252_; lean_object* v_auxDeclNGen_4253_; lean_object* v_traceState_4254_; lean_object* v_messages_4255_; lean_object* v_infoState_4256_; lean_object* v_snapshotTasks_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4273_; 
v___x_4249_ = lean_st_ref_take(v___y_4248_);
v_env_4250_ = lean_ctor_get(v___x_4249_, 0);
v_nextMacroScope_4251_ = lean_ctor_get(v___x_4249_, 1);
v_ngen_4252_ = lean_ctor_get(v___x_4249_, 2);
v_auxDeclNGen_4253_ = lean_ctor_get(v___x_4249_, 3);
v_traceState_4254_ = lean_ctor_get(v___x_4249_, 4);
v_messages_4255_ = lean_ctor_get(v___x_4249_, 6);
v_infoState_4256_ = lean_ctor_get(v___x_4249_, 7);
v_snapshotTasks_4257_ = lean_ctor_get(v___x_4249_, 8);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; 
v_unused_4274_ = lean_ctor_get(v___x_4249_, 5);
lean_dec(v_unused_4274_);
v___x_4259_ = v___x_4249_;
v_isShared_4260_ = v_isSharedCheck_4273_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_snapshotTasks_4257_);
lean_inc(v_infoState_4256_);
lean_inc(v_messages_4255_);
lean_inc(v_traceState_4254_);
lean_inc(v_auxDeclNGen_4253_);
lean_inc(v_ngen_4252_);
lean_inc(v_nextMacroScope_4251_);
lean_inc(v_env_4250_);
lean_dec(v___x_4249_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4273_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4261_; lean_object* v_toEnvExtension_4262_; lean_object* v_asyncMode_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4261_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4262_ = lean_ctor_get(v___x_4261_, 0);
v_asyncMode_4263_ = lean_ctor_get(v_toEnvExtension_4262_, 2);
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v_decl_4240_);
lean_ctor_set(v___x_4264_, 1, v___y_4247_);
v___x_4265_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4261_, v_env_4250_, v___x_4264_, v_asyncMode_4263_, v___x_4235_);
v___x_4266_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 5, v___x_4266_);
lean_ctor_set(v___x_4259_, 0, v___x_4265_);
v___x_4268_ = v___x_4259_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_nextMacroScope_4251_);
lean_ctor_set(v_reuseFailAlloc_4272_, 2, v_ngen_4252_);
lean_ctor_set(v_reuseFailAlloc_4272_, 3, v_auxDeclNGen_4253_);
lean_ctor_set(v_reuseFailAlloc_4272_, 4, v_traceState_4254_);
lean_ctor_set(v_reuseFailAlloc_4272_, 5, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4272_, 6, v_messages_4255_);
lean_ctor_set(v_reuseFailAlloc_4272_, 7, v_infoState_4256_);
lean_ctor_set(v_reuseFailAlloc_4272_, 8, v_snapshotTasks_4257_);
v___x_4268_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = lean_st_ref_set(v___y_4248_, v___x_4268_);
v___x_4270_ = lean_box(0);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
return v___x_4271_;
}
}
}
v___jp_4275_:
{
lean_object* v___x_4279_; lean_object* v_a_4280_; 
lean_inc(v_decl_4240_);
v___x_4279_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_4240_, v___y_4278_);
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref(v___x_4279_);
if (lean_obj_tag(v_a_4280_) == 1)
{
lean_object* v_val_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
lean_dec_ref(v___y_4276_);
lean_dec(v___x_4235_);
v_val_4281_ = lean_ctor_get(v_a_4280_, 0);
lean_inc(v_val_4281_);
lean_dec_ref_known(v_a_4280_, 1);
v___x_4282_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4283_ = 0;
v___x_4284_ = l_Lean_MessageData_ofConstName(v_decl_4240_, v___x_4283_);
v___x_4285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4282_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = l_Lean_stringToMessageData(v_val_4281_);
v___x_4289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4291_, v___y_4277_, v___y_4278_);
return v___x_4292_;
}
else
{
lean_dec(v_a_4280_);
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4278_;
goto v___jp_4246_;
}
}
v___jp_4293_:
{
lean_object* v___x_4297_; lean_object* v_env_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_st_ref_get(v___y_4296_);
v_env_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc_ref(v_env_4298_);
lean_dec(v___x_4297_);
lean_inc(v_decl_4240_);
v___x_4299_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4298_, v_decl_4240_);
if (lean_obj_tag(v___x_4299_) == 1)
{
lean_object* v_val_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec_ref(v___y_4294_);
lean_dec(v___x_4235_);
v_val_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_val_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4302_ = 0;
v___x_4303_ = l_Lean_MessageData_ofConstName(v_decl_4240_, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4301_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = l_Lean_MessageData_ofConstName(v_val_4300_, v___x_4302_);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___x_4301_);
v___x_4310_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4241_, v___x_4309_, v___y_4295_, v___y_4296_);
lean_dec(v_stx_4241_);
return v___x_4310_;
}
else
{
lean_dec(v___x_4299_);
lean_dec(v_stx_4241_);
v___y_4276_ = v___y_4294_;
v___y_4277_ = v___y_4295_;
v___y_4278_ = v___y_4296_;
goto v___jp_4275_;
}
}
v___jp_4311_:
{
lean_object* v___x_4316_; lean_object* v_env_4317_; lean_object* v___x_4318_; 
v___x_4316_ = lean_st_ref_get(v___y_4315_);
v_env_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc_ref(v_env_4317_);
lean_dec(v___x_4316_);
v___x_4318_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4317_, v_decl_4240_);
lean_dec_ref(v_env_4317_);
if (lean_obj_tag(v___x_4318_) == 1)
{
lean_object* v_val_4319_; lean_object* v___x_4320_; lean_object* v_env_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
lean_dec_ref(v___y_4312_);
lean_dec(v___x_4235_);
v_val_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_val_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = lean_st_ref_get(v___y_4315_);
v_env_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc_ref(v_env_4321_);
lean_dec(v___x_4320_);
v___x_4322_ = l_Lean_Environment_allImportedModuleNames(v_env_4321_);
lean_dec_ref(v_env_4321_);
v___x_4323_ = lean_array_get_size(v___x_4322_);
v___x_4324_ = lean_nat_dec_lt(v_val_4319_, v___x_4323_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
lean_dec_ref(v___x_4322_);
lean_dec(v_val_4319_);
v___x_4325_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4326_ = l_Lean_MessageData_ofConstName(v_decl_4240_, v___y_4313_);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4241_, v___x_4329_, v___y_4314_, v___y_4315_);
lean_dec(v_stx_4241_);
return v___x_4330_;
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4331_ = lean_array_fget(v___x_4322_, v_val_4319_);
lean_dec(v_val_4319_);
lean_dec_ref(v___x_4322_);
v___x_4332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4333_ = l_Lean_MessageData_ofConstName(v_decl_4240_, v___y_4313_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_MessageData_ofName(v___x_4331_);
v___x_4338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4241_, v___x_4340_, v___y_4314_, v___y_4315_);
lean_dec(v_stx_4241_);
return v___x_4341_;
}
}
else
{
lean_dec(v___x_4318_);
v___y_4294_ = v___y_4312_;
v___y_4295_ = v___y_4314_;
v___y_4296_ = v___y_4315_;
goto v___jp_4293_;
}
}
v___jp_4342_:
{
lean_object* v___x_4346_; lean_object* v_env_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; 
v___x_4346_ = lean_st_ref_get(v___y_4345_);
v_env_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc_ref(v_env_4347_);
lean_dec(v___x_4346_);
v___x_4348_ = 0;
lean_inc(v_decl_4240_);
v___x_4349_ = l_Lean_Environment_find_x3f(v_env_4347_, v_decl_4240_, v___x_4348_);
if (lean_obj_tag(v___x_4349_) == 0)
{
v___y_4294_ = v_name_4343_;
v___y_4295_ = v___y_4344_;
v___y_4296_ = v___y_4345_;
goto v___jp_4293_;
}
else
{
lean_object* v___x_4350_; lean_object* v_env_4351_; uint8_t v___x_4352_; 
lean_dec_ref_known(v___x_4349_, 1);
v___x_4350_ = lean_st_ref_get(v___y_4345_);
v_env_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc_ref(v_env_4351_);
lean_dec(v___x_4350_);
v___x_4352_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4351_, v_decl_4240_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_dec_ref(v_name_4343_);
lean_dec(v___x_4235_);
v___x_4353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4354_ = l_Lean_MessageData_ofConstName(v_decl_4240_, v___x_4348_);
v___x_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4355_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4241_, v___x_4357_, v___y_4344_, v___y_4345_);
lean_dec(v_stx_4241_);
return v___x_4358_;
}
else
{
v___y_4312_ = v_name_4343_;
v___y_4313_ = v___x_4348_;
v___y_4314_ = v___y_4344_;
v___y_4315_ = v___y_4345_;
goto v___jp_4311_;
}
}
}
v___jp_4359_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4361_ = l_Lean_Name_mkStr4(v___x_4236_, v___x_4237_, v___x_4360_, v___x_4238_);
lean_inc(v_stx_4241_);
v___x_4362_ = l_Lean_Syntax_isOfKind(v_stx_4241_, v___x_4361_);
lean_dec(v___x_4361_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec(v_stx_4241_);
lean_dec(v_decl_4240_);
lean_dec(v___x_4235_);
v___x_4363_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4364_ = l_Lean_MessageData_ofName(v_name_4239_);
v___x_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4365_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4367_, v___y_4243_, v___y_4244_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
else
{
lean_object* v___x_4377_; lean_object* v_name_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4377_ = lean_unsigned_to_nat(1u);
v_name_4378_ = l_Lean_Syntax_getArg(v_stx_4241_, v___x_4377_);
v___x_4379_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4378_);
v___x_4380_ = l_Lean_Syntax_isOfKind(v_name_4378_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4378_);
v___x_4382_ = l_Lean_Syntax_isOfKind(v_name_4378_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_name_4378_);
lean_dec(v_stx_4241_);
lean_dec(v_decl_4240_);
lean_dec(v___x_4235_);
v___x_4383_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4384_ = l_Lean_MessageData_ofName(v_name_4239_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4387_, v___y_4243_, v___y_4244_);
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
else
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_dec(v_name_4239_);
v___x_4397_ = l_Lean_TSyntax_getId(v_name_4378_);
lean_dec(v_name_4378_);
v___x_4398_ = l_Lean_Name_toString(v___x_4397_, v___x_4380_);
v_name_4343_ = v___x_4398_;
v___y_4344_ = v___y_4243_;
v___y_4345_ = v___y_4244_;
goto v___jp_4342_;
}
}
else
{
lean_object* v___x_4399_; 
lean_dec(v_name_4239_);
v___x_4399_ = l_Lean_TSyntax_getString(v_name_4378_);
lean_dec(v_name_4378_);
v_name_4343_ = v___x_4399_;
v___y_4344_ = v___y_4243_;
v___y_4345_ = v___y_4244_;
goto v___jp_4342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v___x_4403_, lean_object* v___x_4404_, lean_object* v___x_4405_, lean_object* v___x_4406_, lean_object* v_name_4407_, lean_object* v_decl_4408_, lean_object* v_stx_4409_, lean_object* v_kind_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v_kind_boxed_4414_; lean_object* v_res_4415_; 
v_kind_boxed_4414_ = lean_unbox(v_kind_4410_);
v_res_4415_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(v___x_4403_, v___x_4404_, v___x_4405_, v___x_4406_, v_name_4407_, v_decl_4408_, v_stx_4409_, v_kind_boxed_4414_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
return v_res_4415_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4427_ = lean_unsigned_to_nat(3374007381u);
v___x_4428_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4429_ = l_Lean_Name_num___override(v___x_4428_, v___x_4427_);
return v___x_4429_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4430_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4431_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4432_ = l_Lean_Name_str___override(v___x_4431_, v___x_4430_);
return v___x_4432_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4434_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4435_ = l_Lean_Name_str___override(v___x_4434_, v___x_4433_);
return v___x_4435_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4436_ = lean_unsigned_to_nat(2u);
v___x_4437_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4438_ = l_Lean_Name_num___override(v___x_4437_, v___x_4436_);
return v___x_4438_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4440_; lean_object* v___x_4441_; lean_object* v_name_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4440_ = 2;
v___x_4441_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v_name_4442_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4443_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4444_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
lean_ctor_set(v___x_4444_, 1, v_name_4442_);
lean_ctor_set(v___x_4444_, 2, v___x_4441_);
lean_ctor_set_uint8(v___x_4444_, sizeof(void*)*3, v___x_4440_);
return v___x_4444_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___f_4445_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___f_4446_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4447_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v___f_4446_);
lean_ctor_set(v___x_4448_, 2, v___f_4445_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4451_ = l_Lean_registerBuiltinAttribute(v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object* v_tac_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4454_, v___y_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tac_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(v_tac_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4464_, lean_object* v_k_4465_, lean_object* v_x_4466_, lean_object* v_x_4467_, lean_object* v_x_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4464_, v_k_4465_, v_x_4466_, v_x_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4470_, lean_object* v_k_4471_, lean_object* v_x_4472_, lean_object* v_x_4473_, lean_object* v_x_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(v_as_4470_, v_k_4471_, v_x_4472_, v_x_4473_, v_x_4474_);
lean_dec_ref(v_k_4471_);
lean_dec_ref(v_as_4470_);
return v_res_4475_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0));
v___x_4478_ = l_Lean_stringToMessageData(v___x_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object* v_catName_4479_, lean_object* v_declName_4480_, uint8_t v___builtIn_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; uint8_t v___x_4486_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; 
v___x_4485_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_4486_ = lean_name_eq(v_catName_4479_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4536_; lean_object* v_env_4544_; lean_object* v___x_4545_; 
v___x_4536_ = lean_st_ref_get(v___y_4483_);
v_env_4544_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_ref(v_env_4544_);
lean_dec(v___x_4536_);
lean_inc(v_declName_4480_);
v___x_4545_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4544_, v_declName_4480_);
if (lean_obj_tag(v___x_4545_) == 0)
{
if (v___x_4486_ == 0)
{
v___y_4524_ = v___y_4482_;
v___y_4525_ = v___y_4483_;
goto v___jp_4523_;
}
else
{
goto v___jp_4537_;
}
}
else
{
lean_dec_ref_known(v___x_4545_, 1);
goto v___jp_4537_;
}
v___jp_4537_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4539_ = l_Lean_MessageData_ofConstName(v_declName_4480_, v___x_4486_);
v___x_4540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4542_, v___y_4482_, v___y_4483_);
return v___x_4543_;
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec(v_declName_4480_);
v___x_4546_ = lean_box(0);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
v___jp_4487_:
{
lean_object* v___x_4490_; lean_object* v_env_4491_; lean_object* v___x_4492_; lean_object* v_toEnvExtension_4493_; lean_object* v_asyncMode_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4490_ = lean_st_ref_get(v___y_4489_);
v_env_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc_ref(v_env_4491_);
lean_dec(v___x_4490_);
v___x_4492_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4493_ = lean_ctor_get(v___x_4492_, 0);
v_asyncMode_4494_ = lean_ctor_get(v_toEnvExtension_4493_, 2);
v___x_4495_ = lean_box(1);
v___x_4496_ = lean_box(0);
v___x_4497_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4495_, v___x_4492_, v_env_4491_, v_asyncMode_4494_, v___x_4496_);
v___x_4498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4497_, v_declName_4480_);
lean_dec(v___x_4497_);
if (lean_obj_tag(v___x_4498_) == 1)
{
lean_object* v_val_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v_val_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4501_ = l_Lean_MessageData_ofConstName(v_declName_4480_, v___x_4486_);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = l_Lean_stringToMessageData(v_val_4499_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v___x_4500_);
v___x_4508_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4507_, v___y_4488_, v___y_4489_);
return v___x_4508_;
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec(v___x_4498_);
lean_dec(v_declName_4480_);
v___x_4509_ = lean_box(0);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
v___jp_4511_:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4515_ = l_Lean_MessageData_ofConstName(v_declName_4480_, v___x_4486_);
v___x_4516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
v___x_4517_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4516_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4518_, v___y_4512_, v___y_4513_);
return v___x_4519_;
}
v___jp_4520_:
{
if (v___x_4486_ == 0)
{
v___y_4488_ = v___y_4521_;
v___y_4489_ = v___y_4522_;
goto v___jp_4487_;
}
else
{
v___y_4512_ = v___y_4521_;
v___y_4513_ = v___y_4522_;
goto v___jp_4511_;
}
}
v___jp_4523_:
{
lean_object* v___x_4526_; lean_object* v_env_4527_; lean_object* v___x_4528_; lean_object* v_toEnvExtension_4529_; lean_object* v_asyncMode_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4526_ = lean_st_ref_get(v___y_4525_);
v_env_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc_ref(v_env_4527_);
lean_dec(v___x_4526_);
v___x_4528_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4529_ = lean_ctor_get(v___x_4528_, 0);
v_asyncMode_4530_ = lean_ctor_get(v_toEnvExtension_4529_, 2);
v___x_4531_ = lean_box(1);
v___x_4532_ = lean_box(0);
v___x_4533_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4531_, v___x_4528_, v_env_4527_, v_asyncMode_4530_, v___x_4532_);
v___x_4534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4533_, v_declName_4480_);
lean_dec(v___x_4533_);
if (lean_obj_tag(v___x_4534_) == 1)
{
lean_object* v_val_4535_; 
v_val_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_val_4535_);
lean_dec_ref_known(v___x_4534_, 1);
if (lean_obj_tag(v_val_4535_) == 0)
{
lean_dec_ref_known(v_val_4535_, 5);
if (v___x_4486_ == 0)
{
v___y_4512_ = v___y_4524_;
v___y_4513_ = v___y_4525_;
goto v___jp_4511_;
}
else
{
v___y_4521_ = v___y_4524_;
v___y_4522_ = v___y_4525_;
goto v___jp_4520_;
}
}
else
{
v___y_4521_ = v___y_4524_;
v___y_4522_ = v___y_4525_;
goto v___jp_4520_;
}
}
else
{
lean_dec(v___x_4534_);
v___y_4488_ = v___y_4524_;
v___y_4489_ = v___y_4525_;
goto v___jp_4487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object* v_catName_4548_, lean_object* v_declName_4549_, lean_object* v___builtIn_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v___builtIn_boxed_4554_; lean_object* v_res_4555_; 
v___builtIn_boxed_4554_ = lean_unbox(v___builtIn_4550_);
v_res_4555_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(v_catName_4548_, v_declName_4549_, v___builtIn_boxed_4554_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v_catName_4548_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4559_; lean_object* v___x_4560_; 
v___f_4559_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0));
v___x_4560_ = l_Lean_Parser_registerParserAttributeHook(v___f_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
return v_res_4562_;
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
res = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
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
