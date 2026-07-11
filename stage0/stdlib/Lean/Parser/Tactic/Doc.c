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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
size_t v_x_355__boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_x_355__boxed_38_ = lean_unbox_usize(v_x_36_);
lean_dec(v_x_36_);
v_res_39_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_35_, v_x_355__boxed_38_, v_x_37_);
lean_dec(v_x_37_);
lean_dec_ref(v_x_35_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; uint64_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1723u);
v___x_42_ = lean_uint64_of_nat(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint64_t v___y_46_; 
if (lean_obj_tag(v_x_44_) == 0)
{
uint64_t v___x_49_; 
v___x_49_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_46_ = v___x_49_;
goto v___jp_45_;
}
else
{
uint64_t v_hash_50_; 
v_hash_50_ = lean_ctor_get_uint64(v_x_44_, sizeof(void*)*2);
v___y_46_ = v_hash_50_;
goto v___jp_45_;
}
v___jp_45_:
{
size_t v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_uint64_to_usize(v___y_46_);
v___x_48_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_43_, v___x_47_, v_x_44_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___boxed(lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_51_, v_x_52_);
lean_dec(v_x_52_);
lean_dec_ref(v_x_51_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_55_, lean_object* v_vals_56_, lean_object* v_i_57_, lean_object* v_k_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_keys_55_);
v___x_60_ = lean_nat_dec_lt(v_i_57_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_i_57_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v_k_x27_62_; uint8_t v___x_63_; 
v_k_x27_62_ = lean_array_fget_borrowed(v_keys_55_, v_i_57_);
v___x_63_ = lean_name_eq(v_k_58_, v_k_x27_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_i_57_, v___x_64_);
lean_dec(v_i_57_);
v_i_57_ = v___x_65_;
goto _start;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_array_fget_borrowed(v_vals_56_, v_i_57_);
lean_dec(v_i_57_);
lean_inc(v___x_67_);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_69_, lean_object* v_vals_70_, lean_object* v_i_71_, lean_object* v_k_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_69_, v_vals_70_, v_i_71_, v_k_72_);
lean_dec(v_k_72_);
lean_dec_ref(v_vals_70_);
lean_dec_ref(v_keys_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(lean_object* v_x_74_, size_t v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_es_77_; lean_object* v___x_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v_j_81_; lean_object* v___x_82_; 
v_es_77_ = lean_ctor_get(v_x_74_, 0);
v___x_78_ = lean_box(2);
v___x_79_ = ((size_t)31ULL);
v___x_80_ = lean_usize_land(v_x_75_, v___x_79_);
v_j_81_ = lean_usize_to_nat(v___x_80_);
v___x_82_ = lean_array_get_borrowed(v___x_78_, v_es_77_, v_j_81_);
lean_dec(v_j_81_);
switch(lean_obj_tag(v___x_82_))
{
case 0:
{
lean_object* v_key_83_; lean_object* v_val_84_; uint8_t v___x_85_; 
v_key_83_ = lean_ctor_get(v___x_82_, 0);
v_val_84_ = lean_ctor_get(v___x_82_, 1);
v___x_85_ = lean_name_eq(v_x_76_, v_key_83_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
lean_inc(v_val_84_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_val_84_);
return v___x_87_;
}
}
case 1:
{
lean_object* v_node_88_; size_t v___x_89_; size_t v___x_90_; 
v_node_88_ = lean_ctor_get(v___x_82_, 0);
v___x_89_ = ((size_t)5ULL);
v___x_90_ = lean_usize_shift_right(v_x_75_, v___x_89_);
v_x_74_ = v_node_88_;
v_x_75_ = v___x_90_;
goto _start;
}
default: 
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
}
else
{
lean_object* v_ks_93_; lean_object* v_vs_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_ks_93_ = lean_ctor_get(v_x_74_, 0);
v_vs_94_ = lean_ctor_get(v_x_74_, 1);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_ks_93_, v_vs_94_, v___x_95_, v_x_76_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg___boxed(lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
size_t v_x_436__boxed_100_; lean_object* v_res_101_; 
v_x_436__boxed_100_ = lean_unbox_usize(v_x_98_);
lean_dec(v_x_98_);
v_res_101_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_97_, v_x_436__boxed_100_, v_x_99_);
lean_dec(v_x_99_);
lean_dec_ref(v_x_97_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint64_t v___y_105_; 
if (lean_obj_tag(v_x_103_) == 0)
{
uint64_t v___x_108_; 
v___x_108_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_105_ = v___x_108_;
goto v___jp_104_;
}
else
{
uint64_t v_hash_109_; 
v_hash_109_ = lean_ctor_get_uint64(v_x_103_, sizeof(void*)*2);
v___y_105_ = v_hash_109_;
goto v___jp_104_;
}
v___jp_104_:
{
size_t v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_uint64_to_usize(v___y_105_);
v___x_107_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_102_, v___x_106_, v_x_103_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec_ref(v_x_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object* v_env_116_, lean_object* v_kind_117_){
_start:
{
lean_object* v___x_118_; lean_object* v_ext_119_; lean_object* v_toEnvExtension_120_; lean_object* v_asyncMode_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_categories_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_118_ = l_Lean_Parser_parserExtension;
v_ext_119_ = lean_ctor_get(v___x_118_, 1);
v_toEnvExtension_120_ = lean_ctor_get(v_ext_119_, 0);
v_asyncMode_121_ = lean_ctor_get(v_toEnvExtension_120_, 2);
v___x_122_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_123_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_122_, v___x_118_, v_env_116_, v_asyncMode_121_);
v_categories_124_ = lean_ctor_get(v___x_123_, 2);
lean_inc_ref(v_categories_124_);
lean_dec(v___x_123_);
v___x_125_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_126_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_categories_124_, v___x_125_);
lean_dec_ref(v_categories_124_);
if (lean_obj_tag(v___x_126_) == 1)
{
lean_object* v_val_127_; lean_object* v_kinds_128_; uint8_t v___x_129_; 
v_val_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v___x_126_, 1);
v_kinds_128_ = lean_ctor_get(v_val_127_, 1);
lean_inc_ref(v_kinds_128_);
lean_dec(v_val_127_);
v___x_129_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_128_, v_kind_117_);
lean_dec_ref(v_kinds_128_);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
lean_dec(v___x_126_);
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_isTactic___boxed(lean_object* v_env_131_, lean_object* v_kind_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_131_, v_kind_132_);
lean_dec(v_kind_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(lean_object* v_00_u03b2_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_136_, v_x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___boxed(lean_object* v_00_u03b2_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(v_00_u03b2_139_, v_x_140_, v_x_141_);
lean_dec(v_x_141_);
lean_dec_ref(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(lean_object* v_00_u03b2_143_, lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_144_, v_x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___boxed(lean_object* v_00_u03b2_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(v_00_u03b2_147_, v_x_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec_ref(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(lean_object* v_00_u03b2_152_, lean_object* v_x_153_, size_t v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_153_, v_x_154_, v_x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___boxed(lean_object* v_00_u03b2_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
size_t v_x_543__boxed_161_; lean_object* v_res_162_; 
v_x_543__boxed_161_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_res_162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(v_00_u03b2_157_, v_x_158_, v_x_543__boxed_161_, v_x_160_);
lean_dec(v_x_160_);
lean_dec_ref(v_x_158_);
return v_res_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(lean_object* v_00_u03b2_163_, lean_object* v_x_164_, size_t v_x_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_164_, v_x_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___boxed(lean_object* v_00_u03b2_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
size_t v_x_554__boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_x_554__boxed_172_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_res_173_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(v_00_u03b2_168_, v_x_169_, v_x_554__boxed_172_, v_x_171_);
lean_dec(v_x_171_);
lean_dec_ref(v_x_169_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_175_, lean_object* v_keys_176_, lean_object* v_vals_177_, lean_object* v_heq_178_, lean_object* v_i_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_176_, v_vals_177_, v_i_179_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_182_, lean_object* v_keys_183_, lean_object* v_vals_184_, lean_object* v_heq_185_, lean_object* v_i_186_, lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(v_00_u03b2_182_, v_keys_183_, v_vals_184_, v_heq_185_, v_i_186_, v_k_187_);
lean_dec(v_k_187_);
lean_dec_ref(v_vals_184_);
lean_dec_ref(v_keys_183_);
return v_res_188_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_189_, lean_object* v_keys_190_, lean_object* v_vals_191_, lean_object* v_heq_192_, lean_object* v_i_193_, lean_object* v_k_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_keys_190_, v_i_193_, v_k_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_196_, lean_object* v_keys_197_, lean_object* v_vals_198_, lean_object* v_heq_199_, lean_object* v_i_200_, lean_object* v_k_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(v_00_u03b2_196_, v_keys_197_, v_vals_198_, v_heq_199_, v_i_200_, v_k_201_);
lean_dec(v_k_201_);
lean_dec_ref(v_vals_198_);
lean_dec_ref(v_keys_197_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_as_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_208_; 
v_fst_206_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_fst_206_);
v_snd_207_ = lean_ctor_get(v_x_205_, 1);
lean_inc(v_snd_207_);
lean_dec_ref(v_x_205_);
v___x_208_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_206_, v_snd_207_, v_as_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_209_, lean_object* v_pivot_210_, lean_object* v_as_211_, lean_object* v_i_212_, lean_object* v_k_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = lean_nat_dec_lt(v_k_213_, v_hi_209_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_k_213_);
v___x_215_ = lean_array_fswap(v_as_211_, v_i_212_, v_hi_209_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_i_212_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v_fst_218_; lean_object* v_fst_219_; uint8_t v___x_220_; 
v___x_217_ = lean_array_fget_borrowed(v_as_211_, v_k_213_);
v_fst_218_ = lean_ctor_get(v___x_217_, 0);
v_fst_219_ = lean_ctor_get(v_pivot_210_, 0);
v___x_220_ = l_Lean_Name_quickLt(v_fst_218_, v_fst_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_k_213_, v___x_221_);
lean_dec(v_k_213_);
v_k_213_ = v___x_222_;
goto _start;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_array_fswap(v_as_211_, v_i_212_, v_k_213_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_i_212_, v___x_225_);
lean_dec(v_i_212_);
v___x_227_ = lean_nat_add(v_k_213_, v___x_225_);
lean_dec(v_k_213_);
v_as_211_ = v___x_224_;
v_i_212_ = v___x_226_;
v_k_213_ = v___x_227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_229_, lean_object* v_pivot_230_, lean_object* v_as_231_, lean_object* v_i_232_, lean_object* v_k_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_229_, v_pivot_230_, v_as_231_, v_i_232_, v_k_233_);
lean_dec_ref(v_pivot_230_);
lean_dec(v_hi_229_);
return v_res_234_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_235_, lean_object* v_x2_236_){
_start:
{
lean_object* v_fst_237_; lean_object* v_fst_238_; uint8_t v___x_239_; 
v_fst_237_ = lean_ctor_get(v_x1_235_, 0);
v_fst_238_ = lean_ctor_get(v_x2_236_, 0);
v___x_239_ = l_Lean_Name_quickLt(v_fst_237_, v_fst_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_240_, lean_object* v_x2_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_240_, v_x2_241_);
lean_dec_ref(v_x2_241_);
lean_dec_ref(v_x1_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_244_, lean_object* v_as_245_, lean_object* v_lo_246_, lean_object* v_hi_247_){
_start:
{
lean_object* v___y_249_; uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_lt(v_lo_246_, v_hi_247_);
if (v___x_259_ == 0)
{
lean_dec(v_lo_246_);
return v_as_245_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_mid_262_; lean_object* v___y_264_; lean_object* v___y_270_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_260_ = lean_nat_add(v_lo_246_, v_hi_247_);
v___x_261_ = lean_unsigned_to_nat(1u);
v_mid_262_ = lean_nat_shiftr(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___x_275_ = lean_array_fget_borrowed(v_as_245_, v_mid_262_);
v___x_276_ = lean_array_fget_borrowed(v_as_245_, v_lo_246_);
v___x_277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
v___y_270_ = v_as_245_;
goto v___jp_269_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_array_fswap(v_as_245_, v_lo_246_, v_mid_262_);
v___y_270_ = v___x_278_;
goto v___jp_269_;
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = lean_array_fget_borrowed(v___y_264_, v_mid_262_);
v___x_266_ = lean_array_fget_borrowed(v___y_264_, v_hi_247_);
v___x_267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_mid_262_);
v___y_249_ = v___y_264_;
goto v___jp_248_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_array_fswap(v___y_264_, v_mid_262_, v_hi_247_);
lean_dec(v_mid_262_);
v___y_249_ = v___x_268_;
goto v___jp_248_;
}
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_array_fget_borrowed(v___y_270_, v_hi_247_);
v___x_272_ = lean_array_fget_borrowed(v___y_270_, v_lo_246_);
v___x_273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
v___y_264_ = v___y_270_;
goto v___jp_263_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_array_fswap(v___y_270_, v_lo_246_, v_hi_247_);
v___y_264_ = v___x_274_;
goto v___jp_263_;
}
}
}
v___jp_248_:
{
lean_object* v_pivot_250_; lean_object* v___x_251_; lean_object* v_fst_252_; lean_object* v_snd_253_; uint8_t v___x_254_; 
v_pivot_250_ = lean_array_fget(v___y_249_, v_hi_247_);
lean_inc_n(v_lo_246_, 2);
v___x_251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_247_, v_pivot_250_, v___y_249_, v_lo_246_, v_lo_246_);
lean_dec(v_pivot_250_);
v_fst_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_fst_252_);
v_snd_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_snd_253_);
lean_dec_ref(v___x_251_);
v___x_254_ = lean_nat_dec_le(v_hi_247_, v_fst_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_244_, v_snd_253_, v_lo_246_, v_fst_252_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_fst_252_, v___x_256_);
lean_dec(v_fst_252_);
v_as_245_ = v___x_255_;
v_lo_246_ = v___x_257_;
goto _start;
}
else
{
lean_dec(v_fst_252_);
lean_dec(v_lo_246_);
return v_snd_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_279_, lean_object* v_as_280_, lean_object* v_lo_281_, lean_object* v_hi_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_279_, v_as_280_, v_lo_281_, v_hi_282_);
lean_dec(v_hi_282_);
lean_dec(v_n_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_k_286_; lean_object* v_v_287_; lean_object* v_l_288_; lean_object* v_r_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_k_286_ = lean_ctor_get(v_x_285_, 1);
v_v_287_ = lean_ctor_get(v_x_285_, 2);
v_l_288_ = lean_ctor_get(v_x_285_, 3);
v_r_289_ = lean_ctor_get(v_x_285_, 4);
v___x_290_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_284_, v_l_288_);
lean_inc(v_v_287_);
lean_inc(v_k_286_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_k_286_);
lean_ctor_set(v___x_291_, 1, v_v_287_);
v___x_292_ = lean_array_push(v___x_290_, v___x_291_);
v_init_284_ = v___x_292_;
v_x_285_ = v_r_289_;
goto _start;
}
else
{
return v_init_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_294_, v_x_295_);
lean_dec(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_299_, lean_object* v_s_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___y_307_; uint8_t v___x_310_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_303_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_302_, v_s_300_);
v___x_304_ = lean_array_get_size(v___x_303_);
v___x_310_ = lean_nat_dec_eq(v___x_304_, v___x_301_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___y_314_; uint8_t v___x_316_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_sub(v___x_304_, v___x_311_);
v___x_316_ = lean_nat_dec_le(v___x_301_, v___x_312_);
if (v___x_316_ == 0)
{
lean_inc(v___x_312_);
v___y_314_ = v___x_312_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___x_301_;
goto v___jp_313_;
}
v___jp_313_:
{
uint8_t v___x_315_; 
v___x_315_ = lean_nat_dec_le(v___y_314_, v___x_312_);
if (v___x_315_ == 0)
{
lean_dec(v___x_312_);
lean_inc(v___y_314_);
v___y_306_ = v___y_314_;
v___y_307_ = v___y_314_;
goto v___jp_305_;
}
else
{
v___y_306_ = v___y_314_;
v___y_307_ = v___x_312_;
goto v___jp_305_;
}
}
}
else
{
lean_object* v___x_317_; 
lean_inc_ref_n(v___x_303_, 2);
v___x_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_317_, 0, v___x_303_);
lean_ctor_set(v___x_317_, 1, v___x_303_);
lean_ctor_set(v___x_317_, 2, v___x_303_);
return v___x_317_;
}
v___jp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_304_, v___x_303_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_inc_ref_n(v___x_308_, 2);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_318_, lean_object* v_s_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_318_, v_s_319_);
lean_dec(v_s_319_);
lean_dec_ref(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_323_);
lean_dec(v_x_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_es_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_327_, v_es_325_);
v___x_329_ = lean_array_get_size(v___x_328_);
v___x_330_ = lean_nat_dec_eq(v___x_329_, v___x_326_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_334_; uint8_t v___x_338_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_sub(v___x_329_, v___x_331_);
v___x_338_ = lean_nat_dec_le(v___x_326_, v___x_332_);
if (v___x_338_ == 0)
{
lean_inc(v___x_332_);
v___y_334_ = v___x_332_;
goto v___jp_333_;
}
else
{
v___y_334_ = v___x_326_;
goto v___jp_333_;
}
v___jp_333_:
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_le(v___y_334_, v___x_332_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v___x_332_);
lean_inc(v___y_334_);
v___x_336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_329_, v___x_328_, v___y_334_, v___y_334_);
lean_dec(v___y_334_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_329_, v___x_328_, v___y_334_, v___x_332_);
lean_dec(v___x_332_);
return v___x_337_;
}
}
}
else
{
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_es_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_es_339_);
lean_dec(v_es_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_347_, lean_object* v_x_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_352_, v_x_353_, v___y_354_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v_x_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_390_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object* v_init_393_, lean_object* v_t_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_393_, v_t_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_396_, lean_object* v_t_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(v_init_396_, v_t_397_);
lean_dec(v_t_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object* v_n_399_, lean_object* v_as_400_, lean_object* v_lo_401_, lean_object* v_hi_402_, lean_object* v_w_403_, lean_object* v_hlo_404_, lean_object* v_hhi_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_399_, v_as_400_, v_lo_401_, v_hi_402_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_407_, lean_object* v_as_408_, lean_object* v_lo_409_, lean_object* v_hi_410_, lean_object* v_w_411_, lean_object* v_hlo_412_, lean_object* v_hhi_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(v_n_407_, v_as_408_, v_lo_409_, v_hi_410_, v_w_411_, v_hlo_412_, v_hhi_413_);
lean_dec(v_hi_410_);
lean_dec(v_n_407_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_415_, lean_object* v_lo_416_, lean_object* v_hi_417_, lean_object* v_hhi_418_, lean_object* v_pivot_419_, lean_object* v_as_420_, lean_object* v_i_421_, lean_object* v_k_422_, lean_object* v_ilo_423_, lean_object* v_ik_424_, lean_object* v_w_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_417_, v_pivot_419_, v_as_420_, v_i_421_, v_k_422_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_427_, lean_object* v_lo_428_, lean_object* v_hi_429_, lean_object* v_hhi_430_, lean_object* v_pivot_431_, lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_k_434_, lean_object* v_ilo_435_, lean_object* v_ik_436_, lean_object* v_w_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(v_n_427_, v_lo_428_, v_hi_429_, v_hhi_430_, v_pivot_431_, v_as_432_, v_i_433_, v_k_434_, v_ilo_435_, v_ik_436_, v_w_437_);
lean_dec_ref(v_pivot_431_);
lean_dec(v_hi_429_);
lean_dec(v_lo_428_);
lean_dec(v_n_427_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object* v_as_439_, lean_object* v_k_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_m_445_; lean_object* v_a_446_; uint8_t v___x_447_; 
v___x_443_ = lean_nat_add(v_x_441_, v_x_442_);
v___x_444_ = lean_unsigned_to_nat(1u);
v_m_445_ = lean_nat_shiftr(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v_a_446_ = lean_array_fget_borrowed(v_as_439_, v_m_445_);
v___x_447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_446_, v_k_440_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
lean_dec(v_x_442_);
v___x_448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_440_, v_a_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_m_445_);
lean_dec(v_x_441_);
lean_inc(v_a_446_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_a_446_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v_m_445_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_nat_sub(v_m_445_, v___x_444_);
lean_dec(v_m_445_);
v___x_453_ = lean_nat_dec_lt(v___x_452_, v_x_441_);
if (v___x_453_ == 0)
{
v_x_442_ = v___x_452_;
goto _start;
}
else
{
lean_object* v___x_455_; 
lean_dec(v___x_452_);
lean_dec(v_x_441_);
v___x_455_ = lean_box(0);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_m_445_);
lean_dec(v_x_441_);
v___x_456_ = lean_box(0);
return v___x_456_;
}
}
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
lean_dec(v_x_441_);
v___x_457_ = lean_nat_add(v_m_445_, v___x_444_);
lean_dec(v_m_445_);
v___x_458_ = lean_nat_dec_le(v___x_457_, v_x_442_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___x_457_);
lean_dec(v_x_442_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
v_x_441_ = v___x_457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object* v_as_461_, lean_object* v_k_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_461_, v_k_462_, v_x_463_, v_x_464_);
lean_dec_ref(v_k_462_);
lean_dec_ref(v_as_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object* v_env_466_, lean_object* v_tac_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_box(1);
v___x_469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_466_, v_tac_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v_toEnvExtension_471_; lean_object* v_asyncMode_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_471_ = lean_ctor_get(v___x_470_, 0);
v_asyncMode_472_ = lean_ctor_get(v_toEnvExtension_471_, 2);
v___x_473_ = lean_box(0);
v___x_474_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_468_, v___x_470_, v_env_466_, v_asyncMode_472_, v___x_473_);
v___x_475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_474_, v_tac_467_);
lean_dec(v_tac_467_);
lean_dec(v___x_474_);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_val_476_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v___x_469_, 1);
v___x_477_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v___x_478_ = 0;
v___x_479_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_468_, v___x_477_, v_env_466_, v_val_476_, v___x_478_);
lean_dec(v_val_476_);
lean_dec_ref(v_env_466_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_array_get_size(v___x_479_);
v___x_482_ = lean_nat_dec_lt(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v___x_479_);
lean_dec(v_tac_467_);
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
lean_dec(v_tac_467_);
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_tac_467_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object* v___x_571_, lean_object* v_toEnvExtension_572_, lean_object* v_env_573_, lean_object* v_asyncMode_574_, lean_object* v___x_575_, lean_object* v_inst_576_, lean_object* v___f_577_, lean_object* v_toBind_578_, lean_object* v___f_579_, lean_object* v_____s_580_){
_start:
{
lean_object* v___x_581_; lean_object* v_importedEntries_582_; size_t v_sz_583_; size_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_581_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_571_, v_toEnvExtension_572_, v_env_573_, v_asyncMode_574_, v___x_575_);
v_importedEntries_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_importedEntries_582_);
lean_dec(v___x_581_);
v_sz_583_ = lean_array_size(v_importedEntries_582_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_576_, v_importedEntries_582_, v___f_577_, v_sz_583_, v___x_584_, v_____s_580_);
v___x_586_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_585_, v___f_579_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object* v___x_587_, lean_object* v_toEnvExtension_588_, lean_object* v_env_589_, lean_object* v_asyncMode_590_, lean_object* v___x_591_, lean_object* v_inst_592_, lean_object* v___f_593_, lean_object* v_toBind_594_, lean_object* v___f_595_, lean_object* v_____s_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(v___x_587_, v_toEnvExtension_588_, v_env_589_, v_asyncMode_590_, v___x_591_, v_inst_592_, v___f_593_, v_toBind_594_, v___f_595_, v_____s_596_);
lean_dec(v_asyncMode_590_);
lean_dec_ref(v_toEnvExtension_588_);
lean_dec_ref(v___x_587_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object* v___x_598_, lean_object* v_inst_599_, lean_object* v___f_600_, lean_object* v_toBind_601_, lean_object* v___f_602_, lean_object* v___x_603_, lean_object* v___f_604_, lean_object* v___f_605_, lean_object* v_env_606_){
_start:
{
lean_object* v___x_607_; lean_object* v_toEnvExtension_608_; lean_object* v_asyncMode_609_; lean_object* v_found_610_; lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_607_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_608_ = lean_ctor_get(v___x_607_, 0);
v_asyncMode_609_ = lean_ctor_get(v_toEnvExtension_608_, 2);
v_found_610_ = l_Lean_NameSet_empty;
v___x_611_ = lean_box(0);
lean_inc_n(v_toBind_601_, 2);
lean_inc_ref(v_inst_599_);
lean_inc(v_asyncMode_609_);
lean_inc_ref(v_env_606_);
lean_inc_ref(v_toEnvExtension_608_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_612_, 0, v___x_598_);
lean_closure_set(v___f_612_, 1, v_toEnvExtension_608_);
lean_closure_set(v___f_612_, 2, v_env_606_);
lean_closure_set(v___f_612_, 3, v_asyncMode_609_);
lean_closure_set(v___f_612_, 4, v___x_611_);
lean_closure_set(v___f_612_, 5, v_inst_599_);
lean_closure_set(v___f_612_, 6, v___f_600_);
lean_closure_set(v___f_612_, 7, v_toBind_601_);
lean_closure_set(v___f_612_, 8, v___f_602_);
v___x_613_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_603_, v___x_607_, v_env_606_, v_asyncMode_609_, v___x_611_);
v___x_614_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_599_, v___f_604_, v_found_610_, v___x_613_);
v___x_615_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_614_, v___f_605_);
v___x_616_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_615_, v___f_612_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(1);
v___x_618_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_tac_621_){
_start:
{
lean_object* v_toApplicative_622_; lean_object* v_toBind_623_; lean_object* v_getEnv_624_; lean_object* v_toPure_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___x_635_; 
v_toApplicative_622_ = lean_ctor_get(v_inst_619_, 0);
v_toBind_623_ = lean_ctor_get(v_inst_619_, 1);
lean_inc_n(v_toBind_623_, 3);
v_getEnv_624_ = lean_ctor_get(v_inst_620_, 0);
lean_inc(v_getEnv_624_);
lean_dec_ref(v_inst_620_);
v_toPure_625_ = lean_ctor_get(v_toApplicative_622_, 1);
v___x_626_ = lean_box(1);
v___x_627_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_625_, 5);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_628_, 0, v_toPure_625_);
lean_inc(v_tac_621_);
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_629_, 0, v_tac_621_);
lean_closure_set(v___f_629_, 1, v_toPure_625_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_630_, 0, v_tac_621_);
lean_closure_set(v___f_630_, 1, v_toPure_625_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_631_, 0, v_toPure_625_);
lean_inc_ref(v_inst_619_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4), 7, 4);
lean_closure_set(v___f_632_, 0, v_inst_619_);
lean_closure_set(v___f_632_, 1, v___f_630_);
lean_closure_set(v___f_632_, 2, v_toBind_623_);
lean_closure_set(v___f_632_, 3, v___f_631_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5), 2, 1);
lean_closure_set(v___f_633_, 0, v_toPure_625_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7), 9, 8);
lean_closure_set(v___f_634_, 0, v___x_627_);
lean_closure_set(v___f_634_, 1, v_inst_619_);
lean_closure_set(v___f_634_, 2, v___f_632_);
lean_closure_set(v___f_634_, 3, v_toBind_623_);
lean_closure_set(v___f_634_, 4, v___f_633_);
lean_closure_set(v___f_634_, 5, v___x_626_);
lean_closure_set(v___f_634_, 6, v___f_629_);
lean_closure_set(v___f_634_, 7, v___f_628_);
v___x_635_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v_getEnv_624_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object* v_m_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_tac_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Parser_Tactic_Doc_aliases___redArg(v_inst_637_, v_inst_638_, v_tac_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_641_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
lean_ctor_set(v___x_646_, 3, v___x_645_);
lean_ctor_set(v___x_646_, 4, v___x_644_);
lean_ctor_set(v___x_646_, 5, v___x_644_);
lean_ctor_set(v___x_646_, 6, v___x_644_);
lean_ctor_set(v___x_646_, 7, v___x_644_);
lean_ctor_set(v___x_646_, 8, v___x_644_);
lean_ctor_set(v___x_646_, 9, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(32u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_650_ = ((size_t)5ULL);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_unsigned_to_nat(32u);
v___x_653_ = lean_mk_empty_array_with_capacity(v___x_652_);
v___x_654_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_655_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_651_);
lean_ctor_set(v___x_655_, 3, v___x_651_);
lean_ctor_set_usize(v___x_655_, 4, v___x_650_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_box(1);
v___x_657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_658_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_env_665_; lean_object* v_options_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_664_ = lean_st_ref_get(v___y_662_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_env_665_);
lean_dec(v___x_664_);
v_options_666_ = lean_ctor_get(v___y_661_, 2);
v___x_667_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_668_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_666_);
v___x_669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_669_, 0, v_env_665_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
lean_ctor_set(v___x_669_, 3, v_options_666_);
v___x_670_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_msgData_660_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msgData_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_ref_681_; lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
v_ref_681_ = lean_ctor_get(v___y_678_, 5);
v___x_682_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_677_, v___y_678_, v___y_679_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_691_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
lean_inc(v_ref_681_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_ref_681_);
lean_ctor_set(v___x_687_, 1, v_a_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_name_703_, lean_object* v_decl_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_708_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_709_ = l_Lean_MessageData_ofName(v_name_703_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_712_, v___y_705_, v___y_706_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_name_714_, lean_object* v_decl_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_name_714_, v_decl_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_decl_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_decl_720_, lean_object* v_x_721_, lean_object* v_____s_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_snd_726_; lean_object* v_fst_727_; lean_object* v_kinds_728_; uint8_t v___x_729_; 
v_snd_726_ = lean_ctor_get(v_x_721_, 1);
lean_inc(v_snd_726_);
v_fst_727_ = lean_ctor_get(v_x_721_, 0);
lean_inc(v_fst_727_);
lean_dec_ref(v_x_721_);
v_kinds_728_ = lean_ctor_get(v_snd_726_, 1);
lean_inc_ref(v_kinds_728_);
lean_dec(v_snd_726_);
v___x_729_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_728_, v_decl_720_);
lean_dec_ref(v_kinds_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_fst_727_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_____s_722_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_array_push(v_____s_722_, v_fst_727_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_decl_735_, lean_object* v_x_736_, lean_object* v_____s_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_decl_735_, v_x_736_, v_____s_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v_decl_735_);
return v_res_741_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(size_t v_sz_745_, size_t v_i_746_, lean_object* v_bs_747_){
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
v___x_752_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(lean_object* v_name_775_, uint8_t v_kind_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___y_786_; 
v___x_780_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1);
v___x_781_ = l_Lean_MessageData_ofName(v_name_775_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
switch(v_kind_776_)
{
case 0:
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4));
v___y_786_ = v___x_793_;
goto v___jp_785_;
}
case 1:
{
lean_object* v___x_794_; 
v___x_794_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5));
v___y_786_ = v___x_794_;
goto v___jp_785_;
}
default: 
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6));
v___y_786_ = v___x_795_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc_ref(v___y_786_);
v___x_787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_787_, 0, v___y_786_);
v___x_788_ = l_Lean_MessageData_ofFormat(v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_784_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_791_, v___y_777_, v___y_778_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___boxed(lean_object* v_name_796_, lean_object* v_kind_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v_kind_boxed_801_; lean_object* v_res_802_; 
v_kind_boxed_801_ = lean_unbox(v_kind_797_);
v_res_802_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_796_, v_kind_boxed_801_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(lean_object* v_f_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_i_806_, lean_object* v_acc_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_keys_804_);
v___x_812_ = lean_nat_dec_lt(v_i_806_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_i_806_);
lean_dec_ref(v_f_803_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v_acc_807_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
else
{
lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v___x_817_; 
v_k_815_ = lean_array_fget_borrowed(v_keys_804_, v_i_806_);
v_v_816_ = lean_array_fget_borrowed(v_vals_805_, v_i_806_);
lean_inc_ref(v_f_803_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v_v_816_);
lean_inc(v_k_815_);
v___x_817_ = lean_apply_6(v_f_803_, v_acc_807_, v_k_815_, v_v_816_, v___y_808_, v___y_809_, lean_box(0));
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
if (lean_obj_tag(v_a_818_) == 0)
{
lean_dec_ref_known(v_a_818_, 1);
lean_dec(v_i_806_);
lean_dec_ref(v_f_803_);
return v___x_817_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_817_, 1);
v_a_819_ = lean_ctor_get(v_a_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v_a_818_, 1);
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = lean_nat_add(v_i_806_, v___x_820_);
lean_dec(v_i_806_);
v_i_806_ = v___x_821_;
v_acc_807_ = v_a_819_;
goto _start;
}
}
else
{
lean_dec(v_i_806_);
lean_dec_ref(v_f_803_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_f_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_i_826_, lean_object* v_acc_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_823_, v_keys_824_, v_vals_825_, v_i_826_, v_acc_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v_vals_825_);
lean_dec_ref(v_keys_824_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_f_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_es_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_860_; 
v_es_838_ = lean_ctor_get(v_x_833_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_833_);
if (v_isSharedCheck_860_ == 0)
{
v___x_840_ = v_x_833_;
v_isShared_841_ = v_isSharedCheck_860_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_es_838_);
lean_dec(v_x_833_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_860_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_array_get_size(v_es_838_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v_es_838_);
lean_dec_ref(v_f_832_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 1);
lean_ctor_set(v___x_840_, 0, v_x_834_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_x_834_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
else
{
uint8_t v___x_849_; 
v___x_849_ = lean_nat_dec_le(v___x_843_, v___x_843_);
if (v___x_849_ == 0)
{
if (v___x_844_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_es_838_);
lean_dec_ref(v_f_832_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 1);
lean_ctor_set(v___x_840_, 0, v_x_834_);
v___x_851_ = v___x_840_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_x_834_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_840_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_843_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_832_, v_es_838_, v___x_854_, v___x_855_, v_x_834_, v___y_835_, v___y_836_);
lean_dec_ref(v_es_838_);
return v___x_856_;
}
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
lean_del_object(v___x_840_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_843_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_832_, v_es_838_, v___x_857_, v___x_858_, v_x_834_, v___y_835_, v___y_836_);
lean_dec_ref(v_es_838_);
return v___x_859_;
}
}
}
}
else
{
lean_object* v_ks_861_; lean_object* v_vs_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_ks_861_ = lean_ctor_get(v_x_833_, 0);
lean_inc_ref(v_ks_861_);
v_vs_862_ = lean_ctor_get(v_x_833_, 1);
lean_inc_ref(v_vs_862_);
lean_dec_ref_known(v_x_833_, 2);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_832_, v_ks_861_, v_vs_862_, v___x_863_, v_x_834_, v___y_835_, v___y_836_);
lean_dec_ref(v_vs_862_);
lean_dec_ref(v_ks_861_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(lean_object* v_f_865_, lean_object* v_as_866_, size_t v_i_867_, size_t v_stop_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_a_874_; lean_object* v___y_879_; uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_eq(v_i_867_, v_stop_868_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_array_uget_borrowed(v_as_866_, v_i_867_);
switch(lean_obj_tag(v___x_883_))
{
case 0:
{
lean_object* v_key_884_; lean_object* v_val_885_; lean_object* v___x_886_; 
v_key_884_ = lean_ctor_get(v___x_883_, 0);
v_val_885_ = lean_ctor_get(v___x_883_, 1);
lean_inc_ref(v_f_865_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v_val_885_);
lean_inc(v_key_884_);
v___x_886_ = lean_apply_6(v_f_865_, v_b_869_, v_key_884_, v_val_885_, v___y_870_, v___y_871_, lean_box(0));
v___y_879_ = v___x_886_;
goto v___jp_878_;
}
case 1:
{
lean_object* v_node_887_; lean_object* v___x_888_; 
v_node_887_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_node_887_);
lean_inc_ref(v_f_865_);
v___x_888_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_865_, v_node_887_, v_b_869_, v___y_870_, v___y_871_);
v___y_879_ = v___x_888_;
goto v___jp_878_;
}
default: 
{
v_a_874_ = v_b_869_;
goto v___jp_873_;
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v_f_865_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_b_869_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
v___jp_873_:
{
size_t v___x_875_; size_t v___x_876_; 
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_867_, v___x_875_);
v_i_867_ = v___x_876_;
v_b_869_ = v_a_874_;
goto _start;
}
v___jp_878_:
{
if (lean_obj_tag(v___y_879_) == 0)
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v___y_879_, 0);
if (lean_obj_tag(v_a_880_) == 0)
{
lean_dec_ref(v_f_865_);
return v___y_879_;
}
else
{
lean_object* v_a_881_; 
lean_inc_ref(v_a_880_);
lean_dec_ref_known(v___y_879_, 1);
v_a_881_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v_a_880_, 1);
v_a_874_ = v_a_881_;
goto v___jp_873_;
}
}
else
{
lean_dec_ref(v_f_865_);
return v___y_879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_f_891_, lean_object* v_as_892_, lean_object* v_i_893_, lean_object* v_stop_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
size_t v_i_boxed_899_; size_t v_stop_boxed_900_; lean_object* v_res_901_; 
v_i_boxed_899_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_stop_boxed_900_ = lean_unbox_usize(v_stop_894_);
lean_dec(v_stop_894_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_891_, v_as_892_, v_i_boxed_899_, v_stop_boxed_900_, v_b_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_902_, v_x_903_, v_x_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_f_909_, lean_object* v_s_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_a_911_);
lean_ctor_set(v___x_916_, 1, v_b_912_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
v___x_917_ = lean_apply_5(v_f_909_, v___x_916_, v_s_910_, v___y_913_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_944_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_944_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_944_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_944_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
if (lean_obj_tag(v_a_918_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v_a_922_ = lean_ctor_get(v_a_918_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_932_ == 0)
{
v___x_924_ = v_a_918_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_a_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_927_);
v___x_929_ = v___x_920_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_943_; 
v_a_933_ = lean_ctor_get(v_a_918_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_918_);
if (v_isSharedCheck_943_ == 0)
{
v___x_935_ = v_a_918_;
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v_a_918_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_938_);
v___x_940_ = v___x_920_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_917_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_917_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_f_953_, lean_object* v_s_954_, lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(v_f_953_, v_s_954_, v_a_955_, v_b_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(lean_object* v_map_961_, lean_object* v_init_962_, lean_object* v_f_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; 
v___f_967_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_967_, 0, v_f_963_);
lean_inc_ref(v_map_961_);
v___x_968_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v___f_967_, v_map_961_, v_init_962_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_a_973_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_a_973_);
lean_dec(v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_a_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_968_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_968_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_map_986_, lean_object* v_init_987_, lean_object* v_f_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_986_, v_init_987_, v_f_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_map_986_);
return v_res_992_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_993_; double v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_float_of_nat(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_cls_998_, lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_ref_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1049_; 
v_ref_1003_ = lean_ctor_get(v___y_1000_, 5);
v___x_1004_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_999_, v___y_1000_, v___y_1001_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1049_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1049_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_traceState_1010_; lean_object* v_env_1011_; lean_object* v_nextMacroScope_1012_; lean_object* v_ngen_1013_; lean_object* v_auxDeclNGen_1014_; lean_object* v_cache_1015_; lean_object* v_messages_1016_; lean_object* v_infoState_1017_; lean_object* v_snapshotTasks_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1048_; 
v___x_1009_ = lean_st_ref_take(v___y_1001_);
v_traceState_1010_ = lean_ctor_get(v___x_1009_, 4);
v_env_1011_ = lean_ctor_get(v___x_1009_, 0);
v_nextMacroScope_1012_ = lean_ctor_get(v___x_1009_, 1);
v_ngen_1013_ = lean_ctor_get(v___x_1009_, 2);
v_auxDeclNGen_1014_ = lean_ctor_get(v___x_1009_, 3);
v_cache_1015_ = lean_ctor_get(v___x_1009_, 5);
v_messages_1016_ = lean_ctor_get(v___x_1009_, 6);
v_infoState_1017_ = lean_ctor_get(v___x_1009_, 7);
v_snapshotTasks_1018_ = lean_ctor_get(v___x_1009_, 8);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1020_ = v___x_1009_;
v_isShared_1021_ = v_isSharedCheck_1048_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snapshotTasks_1018_);
lean_inc(v_infoState_1017_);
lean_inc(v_messages_1016_);
lean_inc(v_cache_1015_);
lean_inc(v_traceState_1010_);
lean_inc(v_auxDeclNGen_1014_);
lean_inc(v_ngen_1013_);
lean_inc(v_nextMacroScope_1012_);
lean_inc(v_env_1011_);
lean_dec(v___x_1009_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1048_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint64_t v_tid_1022_; lean_object* v_traces_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1047_; 
v_tid_1022_ = lean_ctor_get_uint64(v_traceState_1010_, sizeof(void*)*1);
v_traces_1023_ = lean_ctor_get(v_traceState_1010_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_traceState_1010_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1025_ = v_traceState_1010_;
v_isShared_1026_ = v_isSharedCheck_1047_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_traces_1023_);
lean_dec(v_traceState_1010_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1047_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; double v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0);
v___x_1029_ = 0;
v___x_1030_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1031_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1031_, 0, v_cls_998_);
lean_ctor_set(v___x_1031_, 1, v___x_1027_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
lean_ctor_set_float(v___x_1031_, sizeof(void*)*3, v___x_1028_);
lean_ctor_set_float(v___x_1031_, sizeof(void*)*3 + 8, v___x_1028_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*3 + 16, v___x_1029_);
v___x_1032_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2));
v___x_1033_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v_a_1005_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
lean_inc(v_ref_1003_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_ref_1003_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_PersistentArray_push___redArg(v_traces_1023_, v___x_1034_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1035_);
v___x_1037_ = v___x_1025_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1035_);
lean_ctor_set_uint64(v_reuseFailAlloc_1046_, sizeof(void*)*1, v_tid_1022_);
v___x_1037_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 4, v___x_1037_);
v___x_1039_ = v___x_1020_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_env_1011_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_nextMacroScope_1012_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_ngen_1013_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_auxDeclNGen_1014_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_cache_1015_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_messages_1016_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_infoState_1017_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_snapshotTasks_1018_);
v___x_1039_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = lean_st_ref_set(v___y_1001_, v___x_1039_);
v___x_1041_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1041_);
v___x_1043_ = v___x_1007_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_cls_1050_, lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1050_, v_msg_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_keys_1056_, lean_object* v_i_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_array_get_size(v_keys_1056_);
v___x_1060_ = lean_nat_dec_lt(v_i_1057_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec(v_i_1057_);
return v___x_1060_;
}
else
{
lean_object* v_k_x27_1061_; uint8_t v___x_1062_; 
v_k_x27_1061_ = lean_array_fget_borrowed(v_keys_1056_, v_i_1057_);
v___x_1062_ = l_Lean_instBEqExtraModUse_beq(v_k_1058_, v_k_x27_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_i_1057_, v___x_1063_);
lean_dec(v_i_1057_);
v_i_1057_ = v___x_1064_;
goto _start;
}
else
{
lean_dec(v_i_1057_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_keys_1066_, lean_object* v_i_1067_, lean_object* v_k_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1066_, v_i_1067_, v_k_1068_);
lean_dec_ref(v_k_1068_);
lean_dec_ref(v_keys_1066_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_x_1071_, size_t v_x_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v_es_1074_; lean_object* v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; lean_object* v_j_1078_; lean_object* v___x_1079_; 
v_es_1074_ = lean_ctor_get(v_x_1071_, 0);
v___x_1075_ = lean_box(2);
v___x_1076_ = ((size_t)31ULL);
v___x_1077_ = lean_usize_land(v_x_1072_, v___x_1076_);
v_j_1078_ = lean_usize_to_nat(v___x_1077_);
v___x_1079_ = lean_array_get_borrowed(v___x_1075_, v_es_1074_, v_j_1078_);
lean_dec(v_j_1078_);
switch(lean_obj_tag(v___x_1079_))
{
case 0:
{
lean_object* v_key_1080_; uint8_t v___x_1081_; 
v_key_1080_ = lean_ctor_get(v___x_1079_, 0);
v___x_1081_ = l_Lean_instBEqExtraModUse_beq(v_x_1073_, v_key_1080_);
return v___x_1081_;
}
case 1:
{
lean_object* v_node_1082_; size_t v___x_1083_; size_t v___x_1084_; 
v_node_1082_ = lean_ctor_get(v___x_1079_, 0);
v___x_1083_ = ((size_t)5ULL);
v___x_1084_ = lean_usize_shift_right(v_x_1072_, v___x_1083_);
v_x_1071_ = v_node_1082_;
v_x_1072_ = v___x_1084_;
goto _start;
}
default: 
{
uint8_t v___x_1086_; 
v___x_1086_ = 0;
return v___x_1086_;
}
}
}
else
{
lean_object* v_ks_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_ks_1087_ = lean_ctor_get(v_x_1071_, 0);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_ks_1087_, v___x_1088_, v_x_1073_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_12108__boxed_1093_; uint8_t v_res_1094_; lean_object* v_r_1095_; 
v_x_12108__boxed_1093_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1094_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1090_, v_x_12108__boxed_1093_, v_x_1092_);
lean_dec_ref(v_x_1092_);
lean_dec_ref(v_x_1090_);
v_r_1095_ = lean_box(v_res_1094_);
return v_r_1095_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
uint64_t v___x_1098_; size_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = l_Lean_instHashableExtraModUse_hash(v_x_1097_);
v___x_1099_ = lean_uint64_to_usize(v___x_1098_);
v___x_1100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1096_, v___x_1099_, v_x_1097_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1101_, v_x_1102_);
lean_dec_ref(v_x_1102_);
lean_dec_ref(v_x_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1));
v___x_1108_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0));
v___x_1109_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1110_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15(void){
_start:
{
lean_object* v_cls_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_cls_1129_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1130_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14));
v___x_1131_ = l_Lean_Name_append(v___x_1130_, v_cls_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_mod_1142_, uint8_t v_isMeta_1143_, lean_object* v_hint_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v_env_1149_; uint8_t v_isExporting_1150_; lean_object* v___x_1151_; lean_object* v_env_1152_; lean_object* v___x_1153_; lean_object* v_entry_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___y_1159_; lean_object* v___x_1184_; uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1148_ = lean_st_ref_get(v___y_1146_);
v_env_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_env_1149_);
lean_dec(v___x_1148_);
v_isExporting_1150_ = lean_ctor_get_uint8(v_env_1149_, sizeof(void*)*8);
lean_dec_ref(v_env_1149_);
v___x_1151_ = lean_st_ref_get(v___y_1146_);
v_env_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_env_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2);
lean_inc(v_mod_1142_);
v_entry_1154_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1154_, 0, v_mod_1142_);
lean_ctor_set_uint8(v_entry_1154_, sizeof(void*)*1, v_isExporting_1150_);
lean_ctor_set_uint8(v_entry_1154_, sizeof(void*)*1 + 1, v_isMeta_1143_);
v___x_1155_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1156_ = lean_box(1);
v___x_1157_ = lean_box(0);
v___x_1184_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1153_, v___x_1155_, v_env_1152_, v___x_1156_, v___x_1157_);
v___x_1185_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_1184_, v_entry_1154_);
lean_dec(v___x_1184_);
v___x_1186_ = lean_bool_not(v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref_known(v_entry_1154_, 1);
lean_dec(v_hint_1144_);
lean_dec(v_mod_1142_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v_options_1189_; uint8_t v_hasTrace_1190_; 
v_options_1189_ = lean_ctor_get(v___y_1145_, 2);
v_hasTrace_1190_ = lean_ctor_get_uint8(v_options_1189_, sizeof(void*)*1);
if (v_hasTrace_1190_ == 0)
{
lean_dec(v_hint_1144_);
lean_dec(v_mod_1142_);
v___y_1159_ = v___y_1146_;
goto v___jp_1158_;
}
else
{
lean_object* v_inheritedTraceOptions_1191_; lean_object* v_cls_1192_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_inheritedTraceOptions_1191_ = lean_ctor_get(v___y_1145_, 13);
v_cls_1192_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1212_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15);
v___x_1213_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1191_, v_options_1189_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_hint_1144_);
lean_dec(v_mod_1142_);
v___y_1159_ = v___y_1146_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1214_; lean_object* v___y_1216_; 
v___x_1214_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17);
if (v_isExporting_1150_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22));
v___y_1216_ = v___x_1223_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23));
v___y_1216_ = v___x_1224_;
goto v___jp_1215_;
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_inc_ref(v___y_1216_);
v___x_1217_ = l_Lean_stringToMessageData(v___y_1216_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1214_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
if (v_isMeta_1143_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20));
v___y_1199_ = v___x_1220_;
v___y_1200_ = v___x_1221_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1222_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21));
v___y_1199_ = v___x_1220_;
v___y_1200_ = v___x_1222_;
goto v___jp_1198_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1194_);
lean_ctor_set(v___x_1196_, 1, v___y_1195_);
v___x_1197_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1192_, v___x_1196_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_dec_ref_known(v___x_1197_, 1);
v___y_1159_ = v___y_1146_;
goto v___jp_1158_;
}
else
{
lean_dec_ref_known(v_entry_1154_, 1);
return v___x_1197_;
}
}
v___jp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
lean_inc_ref(v___y_1200_);
v___x_1201_ = l_Lean_stringToMessageData(v___y_1200_);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1199_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_MessageData_ofName(v_mod_1142_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_Name_isAnonymous(v_hint_1144_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11);
v___x_1209_ = l_Lean_MessageData_ofName(v_hint_1144_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___y_1194_ = v___x_1206_;
v___y_1195_ = v___x_1210_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1211_; 
lean_dec(v_hint_1144_);
v___x_1211_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12);
v___y_1194_ = v___x_1206_;
v___y_1195_ = v___x_1211_;
goto v___jp_1193_;
}
}
}
}
v___jp_1158_:
{
lean_object* v___x_1160_; lean_object* v_toEnvExtension_1161_; lean_object* v_env_1162_; lean_object* v_nextMacroScope_1163_; lean_object* v_ngen_1164_; lean_object* v_auxDeclNGen_1165_; lean_object* v_traceState_1166_; lean_object* v_messages_1167_; lean_object* v_infoState_1168_; lean_object* v_snapshotTasks_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1182_; 
v___x_1160_ = lean_st_ref_take(v___y_1159_);
v_toEnvExtension_1161_ = lean_ctor_get(v___x_1155_, 0);
v_env_1162_ = lean_ctor_get(v___x_1160_, 0);
v_nextMacroScope_1163_ = lean_ctor_get(v___x_1160_, 1);
v_ngen_1164_ = lean_ctor_get(v___x_1160_, 2);
v_auxDeclNGen_1165_ = lean_ctor_get(v___x_1160_, 3);
v_traceState_1166_ = lean_ctor_get(v___x_1160_, 4);
v_messages_1167_ = lean_ctor_get(v___x_1160_, 6);
v_infoState_1168_ = lean_ctor_get(v___x_1160_, 7);
v_snapshotTasks_1169_ = lean_ctor_get(v___x_1160_, 8);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1160_, 5);
lean_dec(v_unused_1183_);
v___x_1171_ = v___x_1160_;
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_snapshotTasks_1169_);
lean_inc(v_infoState_1168_);
lean_inc(v_messages_1167_);
lean_inc(v_traceState_1166_);
lean_inc(v_auxDeclNGen_1165_);
lean_inc(v_ngen_1164_);
lean_inc(v_nextMacroScope_1163_);
lean_inc(v_env_1162_);
lean_dec(v___x_1160_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_asyncMode_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_asyncMode_1173_ = lean_ctor_get(v_toEnvExtension_1161_, 2);
v___x_1174_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1155_, v_env_1162_, v_entry_1154_, v_asyncMode_1173_, v___x_1157_);
v___x_1175_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 5, v___x_1175_);
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1177_ = v___x_1171_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_nextMacroScope_1163_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_ngen_1164_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_auxDeclNGen_1165_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_traceState_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 5, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 6, v_messages_1167_);
lean_ctor_set(v_reuseFailAlloc_1181_, 7, v_infoState_1168_);
lean_ctor_set(v_reuseFailAlloc_1181_, 8, v_snapshotTasks_1169_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_st_ref_set(v___y_1159_, v___x_1177_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_mod_1225_, lean_object* v_isMeta_1226_, lean_object* v_hint_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_isMeta_boxed_1231_; lean_object* v_res_1232_; 
v_isMeta_boxed_1231_ = lean_unbox(v_isMeta_1226_);
v_res_1232_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_mod_1225_, v_isMeta_boxed_1231_, v_hint_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(lean_object* v___x_1233_, lean_object* v_declName_1234_, lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec(v_declName_1234_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_b_1238_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v_modules_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v_toImport_1249_; lean_object* v_module_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1244_ = l_Lean_Environment_header(v___x_1233_);
v_modules_1245_ = lean_ctor_get(v___x_1244_, 3);
lean_inc_ref(v_modules_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1247_ = lean_array_uget_borrowed(v_as_1235_, v_i_1237_);
v___x_1248_ = lean_array_get(v___x_1246_, v_modules_1245_, v_a_1247_);
lean_dec_ref(v_modules_1245_);
v_toImport_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_toImport_1249_);
lean_dec(v___x_1248_);
v_module_1250_ = lean_ctor_get(v_toImport_1249_, 0);
lean_inc(v_module_1250_);
lean_dec_ref(v_toImport_1249_);
v___x_1251_ = 0;
lean_inc(v_declName_1234_);
v___x_1252_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1250_, v___x_1251_, v_declName_1234_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; 
lean_dec_ref_known(v___x_1252_, 1);
v___x_1253_ = lean_box(0);
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1237_, v___x_1254_);
v_i_1237_ = v___x_1255_;
v_b_1238_ = v___x_1253_;
goto _start;
}
else
{
lean_dec(v_declName_1234_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v___x_1257_, lean_object* v_declName_1258_, lean_object* v_as_1259_, lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_b_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v___x_1257_, v_declName_1258_, v_as_1259_, v_sz_boxed_1266_, v_i_boxed_1267_, v_b_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_as_1259_);
lean_dec_ref(v___x_1257_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
else
{
lean_object* v_key_1272_; lean_object* v_value_1273_; lean_object* v_tail_1274_; uint8_t v___x_1275_; 
v_key_1272_ = lean_ctor_get(v_x_1270_, 0);
v_value_1273_ = lean_ctor_get(v_x_1270_, 1);
v_tail_1274_ = lean_ctor_get(v_x_1270_, 2);
v___x_1275_ = lean_name_eq(v_key_1272_, v_a_1269_);
if (v___x_1275_ == 0)
{
v_x_1270_ = v_tail_1274_;
goto _start;
}
else
{
lean_object* v___x_1277_; 
lean_inc(v_value_1273_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_value_1273_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_a_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1278_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec(v_a_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_buckets_1283_; lean_object* v___x_1284_; uint64_t v___y_1286_; 
v_buckets_1283_ = lean_ctor_get(v_m_1281_, 1);
v___x_1284_ = lean_array_get_size(v_buckets_1283_);
if (lean_obj_tag(v_a_1282_) == 0)
{
uint64_t v___x_1300_; 
v___x_1300_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_1286_ = v___x_1300_;
goto v___jp_1285_;
}
else
{
uint64_t v_hash_1301_; 
v_hash_1301_ = lean_ctor_get_uint64(v_a_1282_, sizeof(void*)*2);
v___y_1286_ = v_hash_1301_;
goto v___jp_1285_;
}
v___jp_1285_:
{
uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v_fold_1289_; uint64_t v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1287_ = 32ULL;
v___x_1288_ = lean_uint64_shift_right(v___y_1286_, v___x_1287_);
v_fold_1289_ = lean_uint64_xor(v___y_1286_, v___x_1288_);
v___x_1290_ = 16ULL;
v___x_1291_ = lean_uint64_shift_right(v_fold_1289_, v___x_1290_);
v___x_1292_ = lean_uint64_xor(v_fold_1289_, v___x_1291_);
v___x_1293_ = lean_uint64_to_usize(v___x_1292_);
v___x_1294_ = lean_usize_of_nat(v___x_1284_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_sub(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_usize_land(v___x_1293_, v___x_1296_);
v___x_1298_ = lean_array_uget_borrowed(v_buckets_1283_, v___x_1297_);
v___x_1299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1282_, v___x_1298_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg___boxed(lean_object* v_m_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_m_1302_);
return v_res_1304_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1));
v___x_1308_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0));
v___x_1309_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1308_, v___x_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(lean_object* v_declName_1312_, uint8_t v_isMeta_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v_env_1321_; lean_object* v___y_1323_; lean_object* v___x_1336_; 
v___x_1317_ = lean_st_ref_get(v___y_1315_);
v_env_1321_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_env_1321_);
lean_dec(v___x_1317_);
v___x_1336_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1321_, v_declName_1312_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_dec_ref(v_env_1321_);
lean_dec(v_declName_1312_);
goto v___jp_1318_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1338_; lean_object* v_modules_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = l_Lean_Environment_header(v_env_1321_);
v_modules_1339_ = lean_ctor_get(v___x_1338_, 3);
lean_inc_ref(v_modules_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = lean_array_get_size(v_modules_1339_);
v___x_1341_ = lean_nat_dec_lt(v_val_1337_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_modules_1339_);
lean_dec(v_val_1337_);
lean_dec_ref(v_env_1321_);
lean_dec(v_declName_1312_);
goto v___jp_1318_;
}
else
{
lean_object* v___x_1342_; lean_object* v_env_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___y_1347_; 
v___x_1342_ = lean_st_ref_get(v___y_1315_);
v_env_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_ref(v_env_1343_);
lean_dec(v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2);
v___x_1345_ = lean_array_fget(v_modules_1339_, v_val_1337_);
lean_dec(v_val_1337_);
lean_dec_ref(v_modules_1339_);
if (v_isMeta_1313_ == 0)
{
lean_dec_ref(v_env_1343_);
v___y_1347_ = v_isMeta_1313_;
goto v___jp_1346_;
}
else
{
uint8_t v___x_1358_; uint8_t v___x_1359_; 
lean_inc(v_declName_1312_);
v___x_1358_ = l_Lean_isMarkedMeta(v_env_1343_, v_declName_1312_);
v___x_1359_ = lean_bool_not(v___x_1358_);
v___y_1347_ = v___x_1359_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v_toImport_1348_; lean_object* v_module_1349_; lean_object* v___x_1350_; 
v_toImport_1348_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref(v_toImport_1348_);
lean_dec(v___x_1345_);
v_module_1349_ = lean_ctor_get(v_toImport_1348_, 0);
lean_inc(v_module_1349_);
lean_dec_ref(v_toImport_1348_);
lean_inc(v_declName_1312_);
v___x_1350_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1349_, v___y_1347_, v_declName_1312_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec_ref_known(v___x_1350_, 1);
v___x_1351_ = l_Lean_indirectModUseExt;
v___x_1352_ = lean_box(1);
v___x_1353_ = lean_box(0);
lean_inc_ref(v_env_1321_);
v___x_1354_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1344_, v___x_1351_, v_env_1321_, v___x_1352_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v___x_1354_, v_declName_1312_);
lean_dec(v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3));
v___y_1323_ = v___x_1356_;
goto v___jp_1322_;
}
else
{
lean_object* v_val_1357_; 
v_val_1357_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1355_, 1);
v___y_1323_ = v_val_1357_;
goto v___jp_1322_;
}
}
else
{
lean_dec_ref(v_env_1321_);
lean_dec(v_declName_1312_);
return v___x_1350_;
}
}
}
}
v___jp_1318_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; size_t v_sz_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_box(0);
v_sz_1325_ = lean_array_size(v___y_1323_);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v_env_1321_, v_declName_1312_, v___y_1323_, v_sz_1325_, v___x_1326_, v___x_1324_, v___y_1314_, v___y_1315_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v_env_1321_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1327_, 0);
lean_dec(v_unused_1335_);
v___x_1329_ = v___x_1327_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v___x_1327_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1324_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1324_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___boxed(lean_object* v_declName_1360_, lean_object* v_isMeta_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_isMeta_boxed_1365_; lean_object* v_res_1366_; 
v_isMeta_boxed_1365_ = lean_unbox(v_isMeta_1361_);
v_res_1366_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_declName_1360_, v_isMeta_boxed_1365_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(lean_object* v_ref_1367_, lean_object* v_msg_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_fileName_1372_; lean_object* v_fileMap_1373_; lean_object* v_options_1374_; lean_object* v_currRecDepth_1375_; lean_object* v_maxRecDepth_1376_; lean_object* v_ref_1377_; lean_object* v_currNamespace_1378_; lean_object* v_openDecls_1379_; lean_object* v_initHeartbeats_1380_; lean_object* v_maxHeartbeats_1381_; lean_object* v_quotContext_1382_; lean_object* v_currMacroScope_1383_; uint8_t v_diag_1384_; lean_object* v_cancelTk_x3f_1385_; uint8_t v_suppressElabErrors_1386_; lean_object* v_inheritedTraceOptions_1387_; lean_object* v_ref_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_fileName_1372_ = lean_ctor_get(v___y_1369_, 0);
v_fileMap_1373_ = lean_ctor_get(v___y_1369_, 1);
v_options_1374_ = lean_ctor_get(v___y_1369_, 2);
v_currRecDepth_1375_ = lean_ctor_get(v___y_1369_, 3);
v_maxRecDepth_1376_ = lean_ctor_get(v___y_1369_, 4);
v_ref_1377_ = lean_ctor_get(v___y_1369_, 5);
v_currNamespace_1378_ = lean_ctor_get(v___y_1369_, 6);
v_openDecls_1379_ = lean_ctor_get(v___y_1369_, 7);
v_initHeartbeats_1380_ = lean_ctor_get(v___y_1369_, 8);
v_maxHeartbeats_1381_ = lean_ctor_get(v___y_1369_, 9);
v_quotContext_1382_ = lean_ctor_get(v___y_1369_, 10);
v_currMacroScope_1383_ = lean_ctor_get(v___y_1369_, 11);
v_diag_1384_ = lean_ctor_get_uint8(v___y_1369_, sizeof(void*)*14);
v_cancelTk_x3f_1385_ = lean_ctor_get(v___y_1369_, 12);
v_suppressElabErrors_1386_ = lean_ctor_get_uint8(v___y_1369_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1387_ = lean_ctor_get(v___y_1369_, 13);
v_ref_1388_ = l_Lean_replaceRef(v_ref_1367_, v_ref_1377_);
lean_inc_ref(v_inheritedTraceOptions_1387_);
lean_inc(v_cancelTk_x3f_1385_);
lean_inc(v_currMacroScope_1383_);
lean_inc(v_quotContext_1382_);
lean_inc(v_maxHeartbeats_1381_);
lean_inc(v_initHeartbeats_1380_);
lean_inc(v_openDecls_1379_);
lean_inc(v_currNamespace_1378_);
lean_inc(v_maxRecDepth_1376_);
lean_inc(v_currRecDepth_1375_);
lean_inc_ref(v_options_1374_);
lean_inc_ref(v_fileMap_1373_);
lean_inc_ref(v_fileName_1372_);
v___x_1389_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1389_, 0, v_fileName_1372_);
lean_ctor_set(v___x_1389_, 1, v_fileMap_1373_);
lean_ctor_set(v___x_1389_, 2, v_options_1374_);
lean_ctor_set(v___x_1389_, 3, v_currRecDepth_1375_);
lean_ctor_set(v___x_1389_, 4, v_maxRecDepth_1376_);
lean_ctor_set(v___x_1389_, 5, v_ref_1388_);
lean_ctor_set(v___x_1389_, 6, v_currNamespace_1378_);
lean_ctor_set(v___x_1389_, 7, v_openDecls_1379_);
lean_ctor_set(v___x_1389_, 8, v_initHeartbeats_1380_);
lean_ctor_set(v___x_1389_, 9, v_maxHeartbeats_1381_);
lean_ctor_set(v___x_1389_, 10, v_quotContext_1382_);
lean_ctor_set(v___x_1389_, 11, v_currMacroScope_1383_);
lean_ctor_set(v___x_1389_, 12, v_cancelTk_x3f_1385_);
lean_ctor_set(v___x_1389_, 13, v_inheritedTraceOptions_1387_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*14, v_diag_1384_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*14 + 1, v_suppressElabErrors_1386_);
v___x_1390_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1368_, v___x_1389_, v___y_1370_);
lean_dec_ref_known(v___x_1389_, 14);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_ref_1391_, lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1391_, v_msg_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v_ref_1391_);
return v_res_1396_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_1399_ = l_Lean_stringToMessageData(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(lean_object* v_attrName_1406_, lean_object* v_declName_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1411_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_1412_ = l_Lean_MessageData_ofName(v_attrName_1406_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = 0;
v___x_1417_ = l_Lean_MessageData_ofConstName(v_declName_1407_, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1415_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1420_, v___y_1408_, v___y_1409_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_attrName_1422_, lean_object* v_declName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1422_, v_declName_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(lean_object* v_as_1428_, size_t v_i_1429_, size_t v_stop_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_eq(v_i_1429_, v_stop_1430_);
if (v___x_1431_ == 0)
{
uint8_t v___x_1432_; uint8_t v___y_1434_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1432_ = 1;
v___x_1439_ = lean_array_uget_borrowed(v_as_1428_, v_i_1429_);
v___x_1440_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_1441_ = lean_name_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
v___y_1434_ = v___x_1432_;
goto v___jp_1433_;
}
else
{
v___y_1434_ = v___x_1431_;
goto v___jp_1433_;
}
v___jp_1433_:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_bool_not(v___y_1434_);
if (v___x_1435_ == 0)
{
size_t v___x_1436_; size_t v___x_1437_; 
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1429_, v___x_1436_);
v_i_1429_ = v___x_1437_;
goto _start;
}
else
{
return v___x_1432_;
}
}
}
else
{
uint8_t v___x_1442_; 
v___x_1442_ = 0;
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object* v_as_1443_, lean_object* v_i_1444_, lean_object* v_stop_1445_){
_start:
{
size_t v_i_boxed_1446_; size_t v_stop_boxed_1447_; uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_i_boxed_1446_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_stop_boxed_1447_ = lean_unbox_usize(v_stop_1445_);
lean_dec(v_stop_1445_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v_as_1443_, v_i_boxed_1446_, v_stop_boxed_1447_);
lean_dec_ref(v_as_1443_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1458_ = l_Lean_stringToMessageData(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1461_ = l_Lean_stringToMessageData(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1468_ = l_Lean_stringToMessageData(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v_name_1480_, lean_object* v_decl_1481_, lean_object* v_stx_1482_, uint8_t v_kind_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; uint8_t v___y_1559_; lean_object* v___f_1567_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1604_; lean_object* v___y_1605_; uint8_t v___x_1645_; uint8_t v___x_1646_; 
lean_inc(v_decl_1481_);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed), 6, 1);
lean_closure_set(v___f_1567_, 0, v_decl_1481_);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_instBEqAttributeKind_beq(v_kind_1483_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v___f_1567_);
lean_dec(v_stx_1482_);
lean_dec(v_decl_1481_);
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec(v___x_1475_);
v___x_1647_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1480_, v_kind_1483_, v___y_1484_, v___y_1485_);
return v___x_1647_;
}
else
{
goto v___jp_1640_;
}
v___jp_1487_:
{
lean_object* v___x_1490_; lean_object* v_env_1491_; lean_object* v_nextMacroScope_1492_; lean_object* v_ngen_1493_; lean_object* v_auxDeclNGen_1494_; lean_object* v_traceState_1495_; lean_object* v_messages_1496_; lean_object* v_infoState_1497_; lean_object* v_snapshotTasks_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1514_; 
v___x_1490_ = lean_st_ref_take(v___y_1489_);
v_env_1491_ = lean_ctor_get(v___x_1490_, 0);
v_nextMacroScope_1492_ = lean_ctor_get(v___x_1490_, 1);
v_ngen_1493_ = lean_ctor_get(v___x_1490_, 2);
v_auxDeclNGen_1494_ = lean_ctor_get(v___x_1490_, 3);
v_traceState_1495_ = lean_ctor_get(v___x_1490_, 4);
v_messages_1496_ = lean_ctor_get(v___x_1490_, 6);
v_infoState_1497_ = lean_ctor_get(v___x_1490_, 7);
v_snapshotTasks_1498_ = lean_ctor_get(v___x_1490_, 8);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1490_, 5);
lean_dec(v_unused_1515_);
v___x_1500_ = v___x_1490_;
v_isShared_1501_ = v_isSharedCheck_1514_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snapshotTasks_1498_);
lean_inc(v_infoState_1497_);
lean_inc(v_messages_1496_);
lean_inc(v_traceState_1495_);
lean_inc(v_auxDeclNGen_1494_);
lean_inc(v_ngen_1493_);
lean_inc(v_nextMacroScope_1492_);
lean_inc(v_env_1491_);
lean_dec(v___x_1490_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1514_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v_toEnvExtension_1503_; lean_object* v_asyncMode_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1502_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1503_ = lean_ctor_get(v___x_1502_, 0);
v_asyncMode_1504_ = lean_ctor_get(v_toEnvExtension_1503_, 2);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_decl_1481_);
lean_ctor_set(v___x_1505_, 1, v___y_1488_);
v___x_1506_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1502_, v_env_1491_, v___x_1505_, v_asyncMode_1504_, v___x_1475_);
v___x_1507_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 5, v___x_1507_);
lean_ctor_set(v___x_1500_, 0, v___x_1506_);
v___x_1509_ = v___x_1500_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_nextMacroScope_1492_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_ngen_1493_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_auxDeclNGen_1494_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_traceState_1495_);
lean_ctor_set(v_reuseFailAlloc_1513_, 5, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1513_, 6, v_messages_1496_);
lean_ctor_set(v_reuseFailAlloc_1513_, 7, v_infoState_1497_);
lean_ctor_set(v_reuseFailAlloc_1513_, 8, v_snapshotTasks_1498_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_st_ref_set(v___y_1489_, v___x_1509_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
}
v___jp_1516_:
{
lean_object* v___x_1520_; lean_object* v_env_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_st_ref_get(v___y_1519_);
v_env_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_ref(v_env_1521_);
lean_dec(v___x_1520_);
lean_inc(v___y_1517_);
v___x_1522_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1521_, v___y_1517_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1525_ = l_Lean_MessageData_ofName(v___y_1517_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Lean_MessageData_ofName(v_val_1523_);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1524_);
v___x_1532_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1531_, v___y_1518_, v___y_1519_);
return v___x_1532_;
}
else
{
lean_dec(v___x_1522_);
v___y_1488_ = v___y_1517_;
v___y_1489_ = v___y_1519_;
goto v___jp_1487_;
}
}
v___jp_1533_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v___y_1535_);
v___x_1539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1540_ = l_Lean_MessageData_ofName(v_decl_1481_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
lean_inc_ref(v___y_1538_);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v___y_1538_);
v___x_1545_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_array_to_list(v___y_1537_);
v___x_1548_ = l_Lean_MessageData_andList(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1551_, v___y_1536_, v___y_1534_);
return v___x_1552_;
}
v___jp_1553_:
{
if (v___y_1559_ == 0)
{
lean_dec_ref(v___y_1556_);
v___y_1517_ = v___y_1555_;
v___y_1518_ = v___y_1557_;
v___y_1519_ = v___y_1554_;
goto v___jp_1516_;
}
else
{
size_t v_sz_1560_; size_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
lean_dec(v___x_1475_);
v_sz_1560_ = lean_array_size(v___y_1556_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_1560_, v___x_1561_, v___y_1556_);
v___x_1563_ = lean_array_get_size(v___x_1562_);
v___x_1564_ = lean_nat_dec_lt(v___y_1558_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___y_1555_;
v___y_1536_ = v___y_1557_;
v___y_1537_ = v___x_1562_;
v___y_1538_ = v___x_1565_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___y_1555_;
v___y_1536_ = v___y_1557_;
v___y_1537_ = v___x_1562_;
v___y_1538_ = v___x_1566_;
goto v___jp_1533_;
}
}
}
v___jp_1568_:
{
lean_object* v___x_1573_; lean_object* v_env_1574_; lean_object* v___x_1575_; lean_object* v_ext_1576_; lean_object* v_toEnvExtension_1577_; lean_object* v_asyncMode_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_categories_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1573_ = lean_st_ref_get(v___y_1572_);
v_env_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc_ref(v_env_1574_);
lean_dec(v___x_1573_);
v___x_1575_ = l_Lean_Parser_parserExtension;
v_ext_1576_ = lean_ctor_get(v___x_1575_, 1);
v_toEnvExtension_1577_ = lean_ctor_get(v_ext_1576_, 0);
v_asyncMode_1578_ = lean_ctor_get(v_toEnvExtension_1577_, 2);
v___x_1579_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1580_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1579_, v___x_1575_, v_env_1574_, v_asyncMode_1578_);
v_categories_1581_ = lean_ctor_get(v___x_1580_, 2);
lean_inc_ref(v_categories_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = lean_mk_empty_array_with_capacity(v___x_1476_);
v___x_1583_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_categories_1581_, v___x_1582_, v___f_1567_, v___y_1571_, v___y_1572_);
lean_dec_ref(v_categories_1581_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; uint8_t v___x_1587_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_array_get_size(v_a_1584_);
v___x_1586_ = lean_nat_dec_eq(v___x_1585_, v___x_1476_);
v___x_1587_ = lean_bool_not(v___x_1586_);
if (v___x_1587_ == 0)
{
lean_dec(v_a_1584_);
v___y_1517_ = v___y_1569_;
v___y_1518_ = v___y_1571_;
v___y_1519_ = v___y_1572_;
goto v___jp_1516_;
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_nat_dec_lt(v___x_1476_, v___x_1585_);
if (v___x_1588_ == 0)
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_bool_not(v___x_1588_);
v___y_1554_ = v___y_1572_;
v___y_1555_ = v___y_1569_;
v___y_1556_ = v_a_1584_;
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___x_1589_;
goto v___jp_1553_;
}
else
{
if (v___x_1588_ == 0)
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_bool_not(v___x_1588_);
v___y_1554_ = v___y_1572_;
v___y_1555_ = v___y_1569_;
v___y_1556_ = v_a_1584_;
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___x_1590_;
goto v___jp_1553_;
}
else
{
size_t v___x_1591_; size_t v___x_1592_; uint8_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = lean_usize_of_nat(v___x_1585_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v_a_1584_, v___x_1591_, v___x_1592_);
v___x_1594_ = lean_bool_not(v___x_1593_);
v___y_1554_ = v___y_1572_;
v___y_1555_ = v___y_1569_;
v___y_1556_ = v_a_1584_;
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___x_1594_;
goto v___jp_1553_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v___y_1569_);
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
v_a_1595_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1583_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
v___jp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1607_ = l_Lean_Name_mkStr4(v___x_1477_, v___x_1478_, v___x_1606_, v___x_1479_);
lean_inc(v_stx_1482_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1607_);
lean_dec(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v___f_1567_);
lean_dec(v_stx_1482_);
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
v___x_1609_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1610_ = l_Lean_MessageData_ofName(v_name_1480_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1613_, v___y_1604_, v___y_1605_);
return v___x_1614_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v_name_1480_);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1615_);
lean_dec(v_stx_1482_);
v___x_1617_ = lean_box(0);
lean_inc(v___x_1616_);
v___x_1618_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1616_, v___x_1617_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_n(v_a_1619_, 2);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = 0;
v___x_1621_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_a_1619_, v___x_1620_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; lean_object* v_env_1623_; uint8_t v___x_1624_; uint8_t v___x_1625_; 
lean_dec_ref_known(v___x_1621_, 1);
v___x_1622_ = lean_st_ref_get(v___y_1605_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1623_, v_a_1619_);
v___x_1625_ = lean_bool_not(v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec(v___x_1616_);
v___y_1569_ = v_a_1619_;
v___y_1570_ = v___x_1615_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref(v___f_1567_);
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
v___x_1626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1627_ = l_Lean_MessageData_ofName(v_a_1619_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v___x_1616_, v___x_1630_, v___y_1604_, v___y_1605_);
lean_dec(v___x_1616_);
return v___x_1631_;
}
}
else
{
lean_dec(v_a_1619_);
lean_dec(v___x_1616_);
lean_dec_ref(v___f_1567_);
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
return v___x_1621_;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v___x_1616_);
lean_dec_ref(v___f_1567_);
lean_dec(v_decl_1481_);
lean_dec(v___x_1475_);
v_a_1632_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1618_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1618_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v_env_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_st_ref_get(v___y_1485_);
v_env_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_ref(v_env_1642_);
lean_dec(v___x_1641_);
v___x_1643_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1642_, v_decl_1481_);
lean_dec_ref(v_env_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
v___y_1604_ = v___y_1484_;
v___y_1605_ = v___y_1485_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1644_; 
lean_dec_ref_known(v___x_1643_, 1);
lean_dec_ref(v___f_1567_);
lean_dec(v_stx_1482_);
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec(v___x_1475_);
v___x_1644_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_name_1480_, v_decl_1481_, v___y_1484_, v___y_1485_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v_name_1653_, lean_object* v_decl_1654_, lean_object* v_stx_1655_, lean_object* v_kind_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v_kind_boxed_1660_; lean_object* v_res_1661_; 
v_kind_boxed_1660_ = lean_unbox(v_kind_1656_);
v_res_1661_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v___x_1648_, v___x_1649_, v___x_1650_, v___x_1651_, v___x_1652_, v_name_1653_, v_decl_1654_, v_stx_1655_, v_kind_boxed_1660_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___x_1649_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1751_ = l_Lean_registerBuiltinAttribute(v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1754_, lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1755_, v___y_1756_, v___y_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(v_00_u03b1_1760_, v_msg_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(lean_object* v_00_u03c3_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_map_1768_, lean_object* v_init_1769_, lean_object* v_f_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_1768_, v_init_1769_, v_f_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03c3_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_map_1777_, lean_object* v_init_1778_, lean_object* v_f_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(v_00_u03c3_1775_, v_00_u03b2_1776_, v_map_1777_, v_init_1778_, v_f_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_map_1777_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1784_, lean_object* v_ref_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1785_, v_msg_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_ref_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(v_00_u03b1_1791_, v_ref_1792_, v_msg_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v_ref_1792_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1798_, lean_object* v_attrName_1799_, lean_object* v_declName_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1799_, v_declName_1800_, v___y_1801_, v___y_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_attrName_1806_, lean_object* v_declName_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(v_00_u03b1_1805_, v_attrName_1806_, v_declName_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(lean_object* v_00_u03b1_1812_, lean_object* v_name_1813_, uint8_t v_kind_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1813_, v_kind_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_name_1820_, lean_object* v_kind_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_kind_boxed_1825_; lean_object* v_res_1826_; 
v_kind_boxed_1825_ = lean_unbox(v_kind_1821_);
v_res_1826_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(v_00_u03b1_1819_, v_name_1820_, v_kind_boxed_1825_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1827_, lean_object* v_f_1828_, lean_object* v_init_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1828_, v_map_1827_, v_init_1829_, v___y_1830_, v___y_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1834_, lean_object* v_f_1835_, lean_object* v_init_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1834_, v_f_1835_, v_init_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1841_, lean_object* v_00_u03c3_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_map_1844_, lean_object* v_f_1845_, lean_object* v_init_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1845_, v_map_1844_, v_init_1846_, v___y_1847_, v___y_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1851_, lean_object* v_00_u03c3_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_map_1854_, lean_object* v_f_1855_, lean_object* v_init_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1851_, v_00_u03c3_1852_, v_00_u03b2_1853_, v_map_1854_, v_f_1855_, v_init_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(lean_object* v_00_u03b2_1861_, lean_object* v_m_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1862_, v_a_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___boxed(lean_object* v_00_u03b2_1865_, lean_object* v_m_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(v_00_u03b2_1865_, v_m_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_m_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1869_, lean_object* v_00_u03c3_1870_, lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_f_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1873_, v_x_1874_, v_x_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1880_, lean_object* v_00_u03c3_1881_, lean_object* v_00_u03b1_1882_, lean_object* v_00_u03b2_1883_, lean_object* v_f_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03c3_1880_, v_00_u03c3_1881_, v_00_u03b1_1882_, v_00_u03b2_1883_, v_f_1884_, v_x_1885_, v_x_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1892_, v_x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
uint8_t v_res_1898_; lean_object* v_r_1899_; 
v_res_1898_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_00_u03b2_1895_, v_x_1896_, v_x_1897_);
lean_dec_ref(v_x_1897_);
lean_dec_ref(v_x_1896_);
v_r_1899_ = lean_box(v_res_1898_);
return v_r_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1900_, lean_object* v_a_1901_, lean_object* v_x_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1901_, v_x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1904_, lean_object* v_a_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(v_00_u03b2_1904_, v_a_1905_, v_x_1906_);
lean_dec(v_x_1906_);
lean_dec(v_a_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(lean_object* v_00_u03b1_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_00_u03c3_1910_, lean_object* v_00_u03c3_1911_, lean_object* v_f_1912_, lean_object* v_as_1913_, size_t v_i_1914_, size_t v_stop_1915_, lean_object* v_b_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_1912_, v_as_1913_, v_i_1914_, v_stop_1915_, v_b_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_00_u03b2_1922_, lean_object* v_00_u03c3_1923_, lean_object* v_00_u03c3_1924_, lean_object* v_f_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_stop_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1928_);
lean_dec(v_stop_1928_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(v_00_u03b1_1921_, v_00_u03b2_1922_, v_00_u03c3_1923_, v_00_u03c3_1924_, v_f_1925_, v_as_1926_, v_i_boxed_1933_, v_stop_boxed_1934_, v_b_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_as_1926_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(lean_object* v_00_u03c3_1936_, lean_object* v_00_u03c3_1937_, lean_object* v_00_u03b1_1938_, lean_object* v_00_u03b2_1939_, lean_object* v_f_1940_, lean_object* v_keys_1941_, lean_object* v_vals_1942_, lean_object* v_heq_1943_, lean_object* v_i_1944_, lean_object* v_acc_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_1940_, v_keys_1941_, v_vals_1942_, v_i_1944_, v_acc_1945_, v___y_1946_, v___y_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03c3_1950_, lean_object* v_00_u03c3_1951_, lean_object* v_00_u03b1_1952_, lean_object* v_00_u03b2_1953_, lean_object* v_f_1954_, lean_object* v_keys_1955_, lean_object* v_vals_1956_, lean_object* v_heq_1957_, lean_object* v_i_1958_, lean_object* v_acc_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(v_00_u03c3_1950_, v_00_u03c3_1951_, v_00_u03b1_1952_, v_00_u03b2_1953_, v_f_1954_, v_keys_1955_, v_vals_1956_, v_heq_1957_, v_i_1958_, v_acc_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec_ref(v_vals_1956_);
lean_dec_ref(v_keys_1955_);
return v_res_1963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1964_, lean_object* v_x_1965_, size_t v_x_1966_, lean_object* v_x_1967_){
_start:
{
uint8_t v___x_1968_; 
v___x_1968_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1965_, v_x_1966_, v_x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
size_t v_x_13509__boxed_1973_; uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_x_13509__boxed_1973_ = lean_unbox_usize(v_x_1971_);
lean_dec(v_x_1971_);
v_res_1974_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(v_00_u03b2_1969_, v_x_1970_, v_x_13509__boxed_1973_, v_x_1972_);
lean_dec_ref(v_x_1972_);
lean_dec_ref(v_x_1970_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(lean_object* v_00_u03b2_1976_, lean_object* v_keys_1977_, lean_object* v_vals_1978_, lean_object* v_heq_1979_, lean_object* v_i_1980_, lean_object* v_k_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1977_, v_i_1980_, v_k_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v_00_u03b2_1983_, lean_object* v_keys_1984_, lean_object* v_vals_1985_, lean_object* v_heq_1986_, lean_object* v_i_1987_, lean_object* v_k_1988_){
_start:
{
uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_res_1989_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(v_00_u03b2_1983_, v_keys_1984_, v_vals_1985_, v_heq_1986_, v_i_1987_, v_k_1988_);
lean_dec_ref(v_k_1988_);
lean_dec_ref(v_vals_1985_);
lean_dec_ref(v_keys_1984_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1995_; 
v_fst_1993_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_fst_1993_);
v_snd_1994_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v_x_1992_);
v___x_1995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1993_, v_snd_1994_, v_as_1991_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1996_, lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1997_) == 0)
{
lean_object* v_k_1998_; lean_object* v_v_1999_; lean_object* v_l_2000_; lean_object* v_r_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_k_1998_ = lean_ctor_get(v_x_1997_, 1);
v_v_1999_ = lean_ctor_get(v_x_1997_, 2);
v_l_2000_ = lean_ctor_get(v_x_1997_, 3);
v_r_2001_ = lean_ctor_get(v_x_1997_, 4);
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1996_, v_l_2000_);
lean_inc(v_v_1999_);
lean_inc(v_k_1998_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_k_1998_);
lean_ctor_set(v___x_2003_, 1, v_v_1999_);
v___x_2004_ = lean_array_push(v___x_2002_, v___x_2003_);
v_init_1996_ = v___x_2004_;
v_x_1997_ = v_r_2001_;
goto _start;
}
else
{
return v_init_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2006_, v_x_2007_);
lean_dec(v_x_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_2009_, lean_object* v_x2_2010_){
_start:
{
lean_object* v_fst_2011_; lean_object* v_fst_2012_; uint8_t v___x_2013_; 
v_fst_2011_ = lean_ctor_get(v_x1_2009_, 0);
v_fst_2012_ = lean_ctor_get(v_x2_2010_, 0);
v___x_2013_ = l_Lean_Name_quickLt(v_fst_2011_, v_fst_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_2014_, lean_object* v_x2_2015_){
_start:
{
uint8_t v_res_2016_; lean_object* v_r_2017_; 
v_res_2016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_2014_, v_x2_2015_);
lean_dec_ref(v_x2_2015_);
lean_dec_ref(v_x1_2014_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_2018_, lean_object* v_pivot_2019_, lean_object* v_as_2020_, lean_object* v_i_2021_, lean_object* v_k_2022_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_nat_dec_lt(v_k_2022_, v_hi_2018_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_k_2022_);
v___x_2024_ = lean_array_fswap(v_as_2020_, v_i_2021_, v_hi_2018_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_i_2021_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; lean_object* v_fst_2027_; lean_object* v_fst_2028_; uint8_t v___x_2029_; 
v___x_2026_ = lean_array_fget_borrowed(v_as_2020_, v_k_2022_);
v_fst_2027_ = lean_ctor_get(v___x_2026_, 0);
v_fst_2028_ = lean_ctor_get(v_pivot_2019_, 0);
v___x_2029_ = l_Lean_Name_quickLt(v_fst_2027_, v_fst_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = lean_nat_add(v_k_2022_, v___x_2030_);
lean_dec(v_k_2022_);
v_k_2022_ = v___x_2031_;
goto _start;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2033_ = lean_array_fswap(v_as_2020_, v_i_2021_, v_k_2022_);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_i_2021_, v___x_2034_);
lean_dec(v_i_2021_);
v___x_2036_ = lean_nat_add(v_k_2022_, v___x_2034_);
lean_dec(v_k_2022_);
v_as_2020_ = v___x_2033_;
v_i_2021_ = v___x_2035_;
v_k_2022_ = v___x_2036_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_2038_, lean_object* v_pivot_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_k_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2038_, v_pivot_2039_, v_as_2040_, v_i_2041_, v_k_2042_);
lean_dec_ref(v_pivot_2039_);
lean_dec(v_hi_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_2044_, lean_object* v_as_2045_, lean_object* v_lo_2046_, lean_object* v_hi_2047_){
_start:
{
lean_object* v___y_2049_; uint8_t v___x_2059_; 
v___x_2059_ = lean_nat_dec_lt(v_lo_2046_, v_hi_2047_);
if (v___x_2059_ == 0)
{
lean_dec(v_lo_2046_);
return v_as_2045_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_mid_2062_; lean_object* v___y_2064_; lean_object* v___y_2070_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2060_ = lean_nat_add(v_lo_2046_, v_hi_2047_);
v___x_2061_ = lean_unsigned_to_nat(1u);
v_mid_2062_ = lean_nat_shiftr(v___x_2060_, v___x_2061_);
lean_dec(v___x_2060_);
v___x_2075_ = lean_array_fget_borrowed(v_as_2045_, v_mid_2062_);
v___x_2076_ = lean_array_fget_borrowed(v_as_2045_, v_lo_2046_);
v___x_2077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_2070_ = v_as_2045_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_array_fswap(v_as_2045_, v_lo_2046_, v_mid_2062_);
v___y_2070_ = v___x_2078_;
goto v___jp_2069_;
}
v___jp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2065_ = lean_array_fget_borrowed(v___y_2064_, v_mid_2062_);
v___x_2066_ = lean_array_fget_borrowed(v___y_2064_, v_hi_2047_);
v___x_2067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_dec(v_mid_2062_);
v___y_2049_ = v___y_2064_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_array_fswap(v___y_2064_, v_mid_2062_, v_hi_2047_);
lean_dec(v_mid_2062_);
v___y_2049_ = v___x_2068_;
goto v___jp_2048_;
}
}
v___jp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2071_ = lean_array_fget_borrowed(v___y_2070_, v_hi_2047_);
v___x_2072_ = lean_array_fget_borrowed(v___y_2070_, v_lo_2046_);
v___x_2073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
v___y_2064_ = v___y_2070_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_array_fswap(v___y_2070_, v_lo_2046_, v_hi_2047_);
v___y_2064_ = v___x_2074_;
goto v___jp_2063_;
}
}
}
v___jp_2048_:
{
lean_object* v_pivot_2050_; lean_object* v___x_2051_; lean_object* v_fst_2052_; lean_object* v_snd_2053_; uint8_t v___x_2054_; 
v_pivot_2050_ = lean_array_fget(v___y_2049_, v_hi_2047_);
lean_inc_n(v_lo_2046_, 2);
v___x_2051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2047_, v_pivot_2050_, v___y_2049_, v_lo_2046_, v_lo_2046_);
lean_dec(v_pivot_2050_);
v_fst_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_fst_2052_);
v_snd_2053_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2051_);
v___x_2054_ = lean_nat_dec_le(v_hi_2047_, v_fst_2052_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2044_, v_snd_2053_, v_lo_2046_, v_fst_2052_);
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_add(v_fst_2052_, v___x_2056_);
lean_dec(v_fst_2052_);
v_as_2045_ = v___x_2055_;
v_lo_2046_ = v___x_2057_;
goto _start;
}
else
{
lean_dec(v_fst_2052_);
lean_dec(v_lo_2046_);
return v_snd_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_2079_, lean_object* v_as_2080_, lean_object* v_lo_2081_, lean_object* v_hi_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2079_, v_as_2080_, v_lo_2081_, v_hi_2082_);
lean_dec(v_hi_2082_);
lean_dec(v_n_2079_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_2086_, lean_object* v_s_2087_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___x_2097_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2090_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2089_, v_s_2087_);
v___x_2091_ = lean_array_get_size(v___x_2090_);
v___x_2097_ = lean_nat_dec_eq(v___x_2091_, v___x_2088_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___y_2101_; uint8_t v___x_2103_; 
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_sub(v___x_2091_, v___x_2098_);
v___x_2103_ = lean_nat_dec_le(v___x_2088_, v___x_2099_);
if (v___x_2103_ == 0)
{
lean_inc(v___x_2099_);
v___y_2101_ = v___x_2099_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v___x_2088_;
goto v___jp_2100_;
}
v___jp_2100_:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_nat_dec_le(v___y_2101_, v___x_2099_);
if (v___x_2102_ == 0)
{
lean_dec(v___x_2099_);
lean_inc(v___y_2101_);
v___y_2093_ = v___y_2101_;
v___y_2094_ = v___y_2101_;
goto v___jp_2092_;
}
else
{
v___y_2093_ = v___y_2101_;
v___y_2094_ = v___x_2099_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v___x_2104_; 
lean_inc_ref_n(v___x_2090_, 2);
v___x_2104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2090_);
lean_ctor_set(v___x_2104_, 1, v___x_2090_);
lean_ctor_set(v___x_2104_, 2, v___x_2090_);
return v___x_2104_;
}
v___jp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2091_, v___x_2090_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_inc_ref_n(v___x_2095_, 2);
v___x_2096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_ctor_set(v___x_2096_, 2, v___x_2095_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_2105_, lean_object* v_s_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_2105_, v_s_2106_);
lean_dec(v_s_2106_);
lean_dec_ref(v_x_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2111_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2110_, v_es_2108_);
v___x_2112_ = lean_array_get_size(v___x_2111_);
v___x_2113_ = lean_nat_dec_eq(v___x_2112_, v___x_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___y_2117_; uint8_t v___x_2121_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_sub(v___x_2112_, v___x_2114_);
v___x_2121_ = lean_nat_dec_le(v___x_2109_, v___x_2115_);
if (v___x_2121_ == 0)
{
lean_inc(v___x_2115_);
v___y_2117_ = v___x_2115_;
goto v___jp_2116_;
}
else
{
v___y_2117_ = v___x_2109_;
goto v___jp_2116_;
}
v___jp_2116_:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_nat_dec_le(v___y_2117_, v___x_2115_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec(v___x_2115_);
lean_inc(v___y_2117_);
v___x_2119_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2112_, v___x_2111_, v___y_2117_, v___y_2117_);
lean_dec(v___y_2117_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2112_, v___x_2111_, v___y_2117_, v___x_2115_);
lean_dec(v___x_2115_);
return v___x_2120_;
}
}
}
else
{
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_2122_);
lean_dec(v_es_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_2124_, lean_object* v_x_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2124_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_2129_, v_x_2130_, v___y_2131_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_x_2130_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2160_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_2163_, lean_object* v_t_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2163_, v_t_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2166_, lean_object* v_t_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_2166_, v_t_2167_);
lean_dec(v_t_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_2169_, lean_object* v_as_2170_, lean_object* v_lo_2171_, lean_object* v_hi_2172_, lean_object* v_w_2173_, lean_object* v_hlo_2174_, lean_object* v_hhi_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2169_, v_as_2170_, v_lo_2171_, v_hi_2172_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_2177_, lean_object* v_as_2178_, lean_object* v_lo_2179_, lean_object* v_hi_2180_, lean_object* v_w_2181_, lean_object* v_hlo_2182_, lean_object* v_hhi_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_2177_, v_as_2178_, v_lo_2179_, v_hi_2180_, v_w_2181_, v_hlo_2182_, v_hhi_2183_);
lean_dec(v_hi_2180_);
lean_dec(v_n_2177_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_2185_, lean_object* v_lo_2186_, lean_object* v_hi_2187_, lean_object* v_hhi_2188_, lean_object* v_pivot_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_k_2192_, lean_object* v_ilo_2193_, lean_object* v_ik_2194_, lean_object* v_w_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2187_, v_pivot_2189_, v_as_2190_, v_i_2191_, v_k_2192_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_2197_, lean_object* v_lo_2198_, lean_object* v_hi_2199_, lean_object* v_hhi_2200_, lean_object* v_pivot_2201_, lean_object* v_as_2202_, lean_object* v_i_2203_, lean_object* v_k_2204_, lean_object* v_ilo_2205_, lean_object* v_ik_2206_, lean_object* v_w_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(v_n_2197_, v_lo_2198_, v_hi_2199_, v_hhi_2200_, v_pivot_2201_, v_as_2202_, v_i_2203_, v_k_2204_, v_ilo_2205_, v_ik_2206_, v_w_2207_);
lean_dec_ref(v_pivot_2201_);
lean_dec(v_hi_2199_);
lean_dec(v_lo_2198_);
lean_dec(v_n_2197_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_2213_, lean_object* v___x_2214_, lean_object* v_toPure_2215_, lean_object* v___f_2216_, lean_object* v_env_2217_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2217_, v_tag_2213_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v_toEnvExtension_2223_; lean_object* v_asyncMode_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v___f_2216_);
v___x_2222_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2223_ = lean_ctor_get(v___x_2222_, 0);
v_asyncMode_2224_ = lean_ctor_get(v_toEnvExtension_2223_, 2);
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2214_, v___x_2222_, v_env_2217_, v_asyncMode_2224_, v___x_2225_);
v___x_2227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2226_, v_tag_2213_);
lean_dec(v_tag_2213_);
lean_dec(v___x_2226_);
v___x_2228_ = lean_apply_2(v_toPure_2215_, lean_box(0), v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_val_2229_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2230_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2231_ = 0;
v___x_2232_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2214_, v___x_2230_, v_env_2217_, v_val_2229_, v___x_2231_);
lean_dec(v_val_2229_);
lean_dec_ref(v_env_2217_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = lean_array_get_size(v___x_2232_);
v___x_2235_ = lean_nat_dec_lt(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v___x_2232_);
lean_dec_ref(v___f_2216_);
lean_dec(v_tag_2213_);
goto v___jp_2218_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_sub(v___x_2234_, v___x_2236_);
v___x_2238_ = lean_nat_dec_le(v___x_2233_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_dec(v___x_2237_);
lean_dec_ref(v___x_2232_);
lean_dec_ref(v___f_2216_);
lean_dec(v_tag_2213_);
goto v___jp_2218_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_tag_2213_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_2242_ = l_Array_binSearchAux___redArg(v___f_2216_, v___x_2241_, v___x_2232_, v___x_2240_, v___x_2233_, v___x_2237_);
lean_dec_ref(v___x_2232_);
if (lean_obj_tag(v___x_2242_) == 0)
{
goto v___jp_2218_;
}
else
{
lean_object* v_val_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2252_; 
v_val_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_val_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_snd_2247_; lean_object* v___x_2249_; 
v_snd_2247_ = lean_ctor_get(v_val_2243_, 1);
lean_inc(v_snd_2247_);
lean_dec(v_val_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_snd_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_snd_2247_);
v___x_2249_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_apply_2(v_toPure_2215_, lean_box(0), v___x_2249_);
return v___x_2250_;
}
}
}
}
}
}
v___jp_2218_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_apply_2(v_toPure_2215_, lean_box(0), v___x_2219_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_tag_2256_){
_start:
{
lean_object* v_toApplicative_2257_; lean_object* v_toBind_2258_; lean_object* v_getEnv_2259_; lean_object* v_toPure_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; 
v_toApplicative_2257_ = lean_ctor_get(v_inst_2254_, 0);
lean_inc_ref(v_toApplicative_2257_);
v_toBind_2258_ = lean_ctor_get(v_inst_2254_, 1);
lean_inc(v_toBind_2258_);
lean_dec_ref(v_inst_2254_);
v_getEnv_2259_ = lean_ctor_get(v_inst_2255_, 0);
lean_inc(v_getEnv_2259_);
lean_dec_ref(v_inst_2255_);
v_toPure_2260_ = lean_ctor_get(v_toApplicative_2257_, 1);
lean_inc(v_toPure_2260_);
lean_dec_ref(v_toApplicative_2257_);
v___f_2261_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0));
v___x_2262_ = lean_box(1);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2263_, 0, v_tag_2256_);
lean_closure_set(v___f_2263_, 1, v___x_2262_);
lean_closure_set(v___f_2263_, 2, v_toPure_2260_);
lean_closure_set(v___f_2263_, 3, v___f_2261_);
v___x_2264_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v_getEnv_2259_, v___f_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_tag_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_2266_, v_inst_2267_, v_tag_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_2270_, lean_object* v_k_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = lean_array_push(v_l_2270_, v_k_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_2274_, lean_object* v_x2_2275_){
_start:
{
uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2276_ = 1;
v___x_2277_ = l_Lean_Name_toString(v_x1_2274_, v___x_2276_);
v___x_2278_ = l_Lean_Name_toString(v_x2_2275_, v___x_2276_);
v___x_2279_ = lean_string_dec_lt(v___x_2277_, v___x_2278_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_2280_, lean_object* v_x2_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_2280_, v_x2_2281_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_2284_, lean_object* v_a_2285_, lean_object* v_b_2286_, lean_object* v_c_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = l_Lean_NameSet_insert(v_c_2287_, v_a_2285_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = lean_apply_2(v_toPure_2284_, lean_box(0), v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_2291_, lean_object* v_a_2292_, lean_object* v_b_2293_, lean_object* v_c_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_2291_, v_a_2292_, v_b_2293_, v_c_2294_);
lean_dec_ref(v_b_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_2296_, lean_object* v_a_2297_, lean_object* v_x_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_fst_2300_; lean_object* v_found_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_fst_2300_ = lean_ctor_get(v_a_2297_, 0);
lean_inc(v_fst_2300_);
lean_dec_ref(v_a_2297_);
v_found_2301_ = l_Lean_NameSet_insert(v___y_2299_, v_fst_2300_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_found_2301_);
v___x_2303_ = lean_apply_2(v_toPure_2296_, lean_box(0), v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_2304_, lean_object* v___f_2305_, lean_object* v_toBind_2306_, lean_object* v___f_2307_, lean_object* v_a_2308_, lean_object* v_x_2309_, lean_object* v___y_2310_){
_start:
{
size_t v_sz_2311_; size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_sz_2311_ = lean_array_size(v_a_2308_);
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2304_, v_a_2308_, v___f_2305_, v_sz_2311_, v___x_2312_, v___y_2310_);
v___x_2314_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v___x_2313_, v___f_2307_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_2315_, lean_object* v___f_2316_, lean_object* v___f_2317_, lean_object* v_____s_2318_){
_start:
{
lean_object* v___y_2320_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2336_; 
if (lean_obj_tag(v_____s_2318_) == 0)
{
lean_object* v_size_2345_; 
v_size_2345_ = lean_ctor_get(v_____s_2318_, 0);
lean_inc(v_size_2345_);
v___y_2336_ = v_size_2345_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v___x_2346_;
goto v___jp_2335_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_array_to_list(v___y_2320_);
v___x_2322_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2321_);
return v___x_2322_;
}
v___jp_2323_:
{
lean_object* v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2316_, v___y_2326_, v___y_2325_, v___y_2324_, v___y_2327_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2327_);
lean_dec(v___y_2326_);
v___y_2320_ = v___x_2328_;
goto v___jp_2319_;
}
v___jp_2329_:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_nat_dec_le(v___y_2333_, v___y_2331_);
if (v___x_2334_ == 0)
{
lean_dec(v___y_2331_);
lean_inc(v___y_2333_);
v___y_2324_ = v___y_2333_;
v___y_2325_ = v___y_2330_;
v___y_2326_ = v___y_2332_;
v___y_2327_ = v___y_2333_;
goto v___jp_2323_;
}
else
{
v___y_2324_ = v___y_2333_;
v___y_2325_ = v___y_2330_;
v___y_2326_ = v___y_2332_;
v___y_2327_ = v___y_2331_;
goto v___jp_2323_;
}
}
v___jp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2337_ = lean_mk_empty_array_with_capacity(v___y_2336_);
lean_dec(v___y_2336_);
v___x_2338_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2317_, v___x_2337_, v_____s_2318_);
v___x_2339_ = lean_array_get_size(v___x_2338_);
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2341_ = lean_nat_dec_eq(v___x_2339_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_sub(v___x_2339_, v___x_2342_);
v___x_2344_ = lean_nat_dec_le(v___x_2340_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_inc(v___x_2343_);
v___y_2330_ = v___x_2338_;
v___y_2331_ = v___x_2343_;
v___y_2332_ = v___x_2339_;
v___y_2333_ = v___x_2343_;
goto v___jp_2329_;
}
else
{
v___y_2330_ = v___x_2338_;
v___y_2331_ = v___x_2343_;
v___y_2332_ = v___x_2339_;
v___y_2333_ = v___x_2340_;
goto v___jp_2329_;
}
}
else
{
lean_dec_ref(v___f_2316_);
v___y_2320_ = v___x_2338_;
goto v___jp_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2347_, lean_object* v_toEnvExtension_2348_, lean_object* v_env_2349_, lean_object* v_asyncMode_2350_, lean_object* v___x_2351_, lean_object* v_inst_2352_, lean_object* v___f_2353_, lean_object* v_toBind_2354_, lean_object* v___f_2355_, lean_object* v_____s_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v_importedEntries_2358_; size_t v_sz_2359_; size_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2357_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2347_, v_toEnvExtension_2348_, v_env_2349_, v_asyncMode_2350_, v___x_2351_);
v_importedEntries_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_ref(v_importedEntries_2358_);
lean_dec(v___x_2357_);
v_sz_2359_ = lean_array_size(v_importedEntries_2358_);
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2352_, v_importedEntries_2358_, v___f_2353_, v_sz_2359_, v___x_2360_, v_____s_2356_);
v___x_2362_ = lean_apply_4(v_toBind_2354_, lean_box(0), lean_box(0), v___x_2361_, v___f_2355_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2363_, lean_object* v_toEnvExtension_2364_, lean_object* v_env_2365_, lean_object* v_asyncMode_2366_, lean_object* v___x_2367_, lean_object* v_inst_2368_, lean_object* v___f_2369_, lean_object* v_toBind_2370_, lean_object* v___f_2371_, lean_object* v_____s_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2363_, v_toEnvExtension_2364_, v_env_2365_, v_asyncMode_2366_, v___x_2367_, v_inst_2368_, v___f_2369_, v_toBind_2370_, v___f_2371_, v_____s_2372_);
lean_dec(v_asyncMode_2366_);
lean_dec_ref(v_toEnvExtension_2364_);
lean_dec_ref(v___x_2363_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2374_, lean_object* v_inst_2375_, lean_object* v___f_2376_, lean_object* v_toBind_2377_, lean_object* v___f_2378_, lean_object* v___x_2379_, lean_object* v___f_2380_, lean_object* v___f_2381_, lean_object* v_env_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v_toEnvExtension_2384_; lean_object* v_asyncMode_2385_; lean_object* v_found_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2383_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2384_ = lean_ctor_get(v___x_2383_, 0);
v_asyncMode_2385_ = lean_ctor_get(v_toEnvExtension_2384_, 2);
v_found_2386_ = l_Lean_NameSet_empty;
v___x_2387_ = lean_box(0);
lean_inc_n(v_toBind_2377_, 2);
lean_inc_ref(v_inst_2375_);
lean_inc(v_asyncMode_2385_);
lean_inc_ref(v_env_2382_);
lean_inc_ref(v_toEnvExtension_2384_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2388_, 0, v___x_2374_);
lean_closure_set(v___f_2388_, 1, v_toEnvExtension_2384_);
lean_closure_set(v___f_2388_, 2, v_env_2382_);
lean_closure_set(v___f_2388_, 3, v_asyncMode_2385_);
lean_closure_set(v___f_2388_, 4, v___x_2387_);
lean_closure_set(v___f_2388_, 5, v_inst_2375_);
lean_closure_set(v___f_2388_, 6, v___f_2376_);
lean_closure_set(v___f_2388_, 7, v_toBind_2377_);
lean_closure_set(v___f_2388_, 8, v___f_2378_);
v___x_2389_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2379_, v___x_2383_, v_env_2382_, v_asyncMode_2385_, v___x_2387_);
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2375_, v___f_2380_, v_found_2386_, v___x_2389_);
v___x_2391_ = lean_apply_4(v_toBind_2377_, lean_box(0), lean_box(0), v___x_2390_, v___f_2381_);
v___x_2392_ = lean_apply_4(v_toBind_2377_, lean_box(0), lean_box(0), v___x_2391_, v___f_2388_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_box(1);
v___x_2396_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2397_, lean_object* v_inst_2398_){
_start:
{
lean_object* v_toApplicative_2399_; lean_object* v_toBind_2400_; lean_object* v_getEnv_2401_; lean_object* v_toPure_2402_; lean_object* v___f_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; 
v_toApplicative_2399_ = lean_ctor_get(v_inst_2397_, 0);
v_toBind_2400_ = lean_ctor_get(v_inst_2397_, 1);
lean_inc_n(v_toBind_2400_, 3);
v_getEnv_2401_ = lean_ctor_get(v_inst_2398_, 0);
lean_inc(v_getEnv_2401_);
lean_dec_ref(v_inst_2398_);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2399_, 1);
v___f_2403_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2404_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2405_ = lean_box(1);
v___x_2406_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2402_, 5);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2407_, 0, v_toPure_2402_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2408_, 0, v_toPure_2402_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2409_, 0, v_toPure_2402_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2410_, 0, v_toPure_2402_);
lean_inc_ref(v_inst_2397_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2411_, 0, v_inst_2397_);
lean_closure_set(v___f_2411_, 1, v___f_2409_);
lean_closure_set(v___f_2411_, 2, v_toBind_2400_);
lean_closure_set(v___f_2411_, 3, v___f_2410_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2412_, 0, v_toPure_2402_);
lean_closure_set(v___f_2412_, 1, v___f_2404_);
lean_closure_set(v___f_2412_, 2, v___f_2403_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2413_, 0, v___x_2406_);
lean_closure_set(v___f_2413_, 1, v_inst_2397_);
lean_closure_set(v___f_2413_, 2, v___f_2411_);
lean_closure_set(v___f_2413_, 3, v_toBind_2400_);
lean_closure_set(v___f_2413_, 4, v___f_2412_);
lean_closure_set(v___f_2413_, 5, v___x_2405_);
lean_closure_set(v___f_2413_, 6, v___f_2408_);
lean_closure_set(v___f_2413_, 7, v___f_2407_);
v___x_2414_ = lean_apply_4(v_toBind_2400_, lean_box(0), lean_box(0), v_getEnv_2401_, v___f_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2416_, v_inst_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2419_, lean_object* v_k_2420_, lean_object* v_v_2421_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_k_2420_);
lean_ctor_set(v___x_2422_, 1, v_v_2421_);
v___x_2423_ = lean_array_push(v_arr_2419_, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2424_, lean_object* v_x2_2425_){
_start:
{
lean_object* v_fst_2426_; lean_object* v_fst_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_fst_2426_ = lean_ctor_get(v_x1_2424_, 0);
lean_inc(v_fst_2426_);
lean_dec_ref(v_x1_2424_);
v_fst_2427_ = lean_ctor_get(v_x2_2425_, 0);
lean_inc(v_fst_2427_);
lean_dec_ref(v_x2_2425_);
v___x_2428_ = 1;
v___x_2429_ = l_Lean_Name_toString(v_fst_2426_, v___x_2428_);
v___x_2430_ = l_Lean_Name_toString(v_fst_2427_, v___x_2428_);
v___x_2431_ = lean_string_dec_lt(v___x_2429_, v___x_2430_);
lean_dec_ref(v___x_2430_);
lean_dec_ref(v___x_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2432_, lean_object* v_x2_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2432_, v_x2_2433_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_, lean_object* v_c_2439_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2437_, v_b_2438_, v_c_2439_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
v___x_2442_ = lean_apply_2(v_toPure_2436_, lean_box(0), v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2443_, lean_object* v_a_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v_found_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_fst_2447_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_snd_2448_);
lean_dec_ref(v_a_2444_);
v_found_2449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2447_, v_snd_2448_, v___y_2446_);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_found_2449_);
v___x_2451_ = lean_apply_2(v_toPure_2443_, lean_box(0), v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2452_, lean_object* v___f_2453_, lean_object* v___f_2454_, lean_object* v_____s_2455_){
_start:
{
lean_object* v___y_2457_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_arr_2462_; lean_object* v___x_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; uint8_t v___x_2468_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2462_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2453_, v___x_2461_, v_____s_2455_);
v___x_2463_ = lean_array_get_size(v_arr_2462_);
v___x_2468_ = lean_nat_dec_eq(v___x_2463_, v___x_2460_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___y_2472_; uint8_t v___x_2474_; 
v___x_2469_ = lean_unsigned_to_nat(1u);
v___x_2470_ = lean_nat_sub(v___x_2463_, v___x_2469_);
v___x_2474_ = lean_nat_dec_le(v___x_2460_, v___x_2470_);
if (v___x_2474_ == 0)
{
lean_inc(v___x_2470_);
v___y_2472_ = v___x_2470_;
goto v___jp_2471_;
}
else
{
v___y_2472_ = v___x_2460_;
goto v___jp_2471_;
}
v___jp_2471_:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_nat_dec_le(v___y_2472_, v___x_2470_);
if (v___x_2473_ == 0)
{
lean_dec(v___x_2470_);
lean_inc(v___y_2472_);
v___y_2465_ = v___y_2472_;
v___y_2466_ = v___y_2472_;
goto v___jp_2464_;
}
else
{
v___y_2465_ = v___y_2472_;
v___y_2466_ = v___x_2470_;
goto v___jp_2464_;
}
}
}
else
{
lean_dec_ref(v___f_2454_);
v___y_2457_ = v_arr_2462_;
goto v___jp_2456_;
}
v___jp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_array_to_list(v___y_2457_);
v___x_2459_ = lean_apply_2(v_toPure_2452_, lean_box(0), v___x_2458_);
return v___x_2459_;
}
v___jp_2464_:
{
lean_object* v___x_2467_; 
v___x_2467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2454_, v___x_2463_, v_arr_2462_, v___y_2465_, v___y_2466_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2466_);
v___y_2457_ = v___x_2467_;
goto v___jp_2456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2475_, lean_object* v_inst_2476_, lean_object* v___f_2477_, lean_object* v_toBind_2478_, lean_object* v___f_2479_, lean_object* v___x_2480_, lean_object* v___f_2481_, lean_object* v___f_2482_, lean_object* v_env_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v_toEnvExtension_2485_; lean_object* v_asyncMode_2486_; lean_object* v_found_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2484_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2485_ = lean_ctor_get(v___x_2484_, 0);
v_asyncMode_2486_ = lean_ctor_get(v_toEnvExtension_2485_, 2);
v_found_2487_ = lean_box(1);
v___x_2488_ = lean_box(0);
lean_inc_n(v_toBind_2478_, 2);
lean_inc_ref(v_inst_2476_);
lean_inc(v_asyncMode_2486_);
lean_inc_ref(v_env_2483_);
lean_inc_ref(v_toEnvExtension_2485_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2489_, 0, v___x_2475_);
lean_closure_set(v___f_2489_, 1, v_toEnvExtension_2485_);
lean_closure_set(v___f_2489_, 2, v_env_2483_);
lean_closure_set(v___f_2489_, 3, v_asyncMode_2486_);
lean_closure_set(v___f_2489_, 4, v___x_2488_);
lean_closure_set(v___f_2489_, 5, v_inst_2476_);
lean_closure_set(v___f_2489_, 6, v___f_2477_);
lean_closure_set(v___f_2489_, 7, v_toBind_2478_);
lean_closure_set(v___f_2489_, 8, v___f_2479_);
v___x_2490_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2480_, v___x_2484_, v_env_2483_, v_asyncMode_2486_, v___x_2488_);
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2476_, v___f_2481_, v_found_2487_, v___x_2490_);
v___x_2492_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v___x_2491_, v___f_2482_);
v___x_2493_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v___x_2492_, v___f_2489_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2496_, lean_object* v_inst_2497_){
_start:
{
lean_object* v_toApplicative_2498_; lean_object* v_toBind_2499_; lean_object* v_getEnv_2500_; lean_object* v_toPure_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; 
v_toApplicative_2498_ = lean_ctor_get(v_inst_2496_, 0);
v_toBind_2499_ = lean_ctor_get(v_inst_2496_, 1);
lean_inc_n(v_toBind_2499_, 3);
v_getEnv_2500_ = lean_ctor_get(v_inst_2497_, 0);
lean_inc(v_getEnv_2500_);
lean_dec_ref(v_inst_2497_);
v_toPure_2501_ = lean_ctor_get(v_toApplicative_2498_, 1);
v___f_2502_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2503_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2504_ = lean_box(1);
v___x_2505_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2501_, 5);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2506_, 0, v_toPure_2501_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2507_, 0, v_toPure_2501_);
v___f_2508_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2508_, 0, v_toPure_2501_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2509_, 0, v_toPure_2501_);
lean_inc_ref(v_inst_2496_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2510_, 0, v_inst_2496_);
lean_closure_set(v___f_2510_, 1, v___f_2508_);
lean_closure_set(v___f_2510_, 2, v_toBind_2499_);
lean_closure_set(v___f_2510_, 3, v___f_2509_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2511_, 0, v_toPure_2501_);
lean_closure_set(v___f_2511_, 1, v___f_2502_);
lean_closure_set(v___f_2511_, 2, v___f_2503_);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2512_, 0, v___x_2505_);
lean_closure_set(v___f_2512_, 1, v_inst_2496_);
lean_closure_set(v___f_2512_, 2, v___f_2510_);
lean_closure_set(v___f_2512_, 3, v_toBind_2499_);
lean_closure_set(v___f_2512_, 4, v___f_2511_);
lean_closure_set(v___f_2512_, 5, v___x_2504_);
lean_closure_set(v___f_2512_, 6, v___f_2507_);
lean_closure_set(v___f_2512_, 7, v___f_2506_);
v___x_2513_ = lean_apply_4(v_toBind_2499_, lean_box(0), lean_box(0), v_getEnv_2500_, v___f_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2515_, v_inst_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2518_, lean_object* v_init_2519_, lean_object* v_x_2520_){
_start:
{
if (lean_obj_tag(v_x_2520_) == 0)
{
lean_object* v_k_2521_; lean_object* v_l_2522_; lean_object* v_r_2523_; lean_object* v___x_2524_; lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_k_2521_ = lean_ctor_get(v_x_2520_, 1);
v_l_2522_ = lean_ctor_get(v_x_2520_, 3);
v_r_2523_ = lean_ctor_get(v_x_2520_, 4);
lean_inc_n(v_a_2518_, 2);
v___x_2524_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2518_, v_init_2519_, v_l_2522_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
lean_inc(v_k_2521_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_a_2518_);
lean_ctor_set(v___x_2526_, 1, v_k_2521_);
v___x_2527_ = lean_array_push(v_a_2525_, v___x_2526_);
v_init_2519_ = v___x_2527_;
v_x_2520_ = v_r_2523_;
goto _start;
}
else
{
lean_object* v___x_2529_; 
lean_dec(v_a_2518_);
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_init_2519_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2530_, lean_object* v_init_2531_, lean_object* v_x_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2530_, v_init_2531_, v_x_2532_);
lean_dec(v_x_2532_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2534_, lean_object* v_x_2535_){
_start:
{
if (lean_obj_tag(v_x_2535_) == 0)
{
lean_object* v_k_2536_; lean_object* v_v_2537_; lean_object* v_l_2538_; lean_object* v_r_2539_; lean_object* v___x_2540_; lean_object* v_a_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; 
v_k_2536_ = lean_ctor_get(v_x_2535_, 1);
lean_inc(v_k_2536_);
v_v_2537_ = lean_ctor_get(v_x_2535_, 2);
lean_inc(v_v_2537_);
v_l_2538_ = lean_ctor_get(v_x_2535_, 3);
lean_inc(v_l_2538_);
v_r_2539_ = lean_ctor_get(v_x_2535_, 4);
lean_inc(v_r_2539_);
lean_dec_ref_known(v_x_2535_, 5);
v___x_2540_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2534_, v_l_2538_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
v___x_2542_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2536_, v_a_2541_, v_v_2537_);
lean_dec(v_v_2537_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v_init_2534_ = v_a_2543_;
v_x_2535_ = v_r_2539_;
goto _start;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_init_2534_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2546_){
_start:
{
lean_object* v_exported_2547_; lean_object* v___x_2548_; lean_object* v_a_2549_; 
v_exported_2547_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2548_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2547_, v_tags_2546_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
return v_a_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2550_, lean_object* v_s_2551_){
_start:
{
lean_object* v_exported_2552_; lean_object* v___x_2553_; lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_exported_2552_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2553_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2552_, v_s_2551_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_n(v_a_2554_, 3);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2555_, 0, v_a_2554_);
lean_ctor_set(v___x_2555_, 1, v_a_2554_);
lean_ctor_set(v___x_2555_, 2, v_a_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2556_, lean_object* v_s_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2556_, v_s_2557_);
lean_dec_ref(v_x_2556_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2559_, lean_object* v_k_2560_, lean_object* v_fallback_2561_){
_start:
{
if (lean_obj_tag(v_t_2559_) == 0)
{
lean_object* v_k_2562_; lean_object* v_v_2563_; lean_object* v_l_2564_; lean_object* v_r_2565_; uint8_t v___x_2566_; 
v_k_2562_ = lean_ctor_get(v_t_2559_, 1);
v_v_2563_ = lean_ctor_get(v_t_2559_, 2);
v_l_2564_ = lean_ctor_get(v_t_2559_, 3);
v_r_2565_ = lean_ctor_get(v_t_2559_, 4);
v___x_2566_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2560_, v_k_2562_);
switch(v___x_2566_)
{
case 0:
{
v_t_2559_ = v_l_2564_;
goto _start;
}
case 1:
{
lean_inc(v_v_2563_);
return v_v_2563_;
}
default: 
{
v_t_2559_ = v_r_2565_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2561_);
return v_fallback_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2569_, lean_object* v_k_2570_, lean_object* v_fallback_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2569_, v_k_2570_, v_fallback_2571_);
lean_dec(v_fallback_2571_);
lean_dec(v_k_2570_);
lean_dec(v_t_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2573_, lean_object* v_x_2574_){
_start:
{
lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_fst_2575_ = lean_ctor_get(v_x_2574_, 0);
lean_inc(v_fst_2575_);
v_snd_2576_ = lean_ctor_get(v_x_2574_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v_x_2574_);
v___x_2577_ = l_Lean_NameSet_empty;
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2573_, v_fst_2575_, v___x_2577_);
v___x_2579_ = l_Lean_NameSet_insert(v___x_2578_, v_snd_2576_);
v___x_2580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2575_, v___x_2579_, v_tags_2573_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2605_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2608_, lean_object* v_t_2609_, lean_object* v_k_2610_, lean_object* v_fallback_2611_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2609_, v_k_2610_, v_fallback_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2613_, lean_object* v_t_2614_, lean_object* v_k_2615_, lean_object* v_fallback_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2613_, v_t_2614_, v_k_2615_, v_fallback_2616_);
lean_dec(v_fallback_2616_);
lean_dec(v_k_2615_);
lean_dec(v_t_2614_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v_name_2618_, lean_object* v_decl_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2624_ = l_Lean_MessageData_ofName(v_name_2618_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_2627_, v___y_2620_, v___y_2621_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_name_2629_, lean_object* v_decl_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v_name_2629_, v_decl_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v_decl_2630_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
if (lean_obj_tag(v_a_2635_) == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = l_List_reverse___redArg(v_a_2636_);
return v___x_2637_;
}
else
{
lean_object* v_head_2638_; lean_object* v_tail_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2651_; 
v_head_2638_ = lean_ctor_get(v_a_2635_, 0);
v_tail_2639_ = lean_ctor_get(v_a_2635_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_a_2635_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2641_ = v_a_2635_;
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_tail_2639_);
lean_inc(v_head_2638_);
lean_dec(v_a_2635_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2651_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2644_ = l_Lean_MessageData_ofName(v_head_2638_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v___x_2643_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v_a_2636_);
lean_ctor_set(v___x_2641_, 0, v___x_2646_);
v___x_2648_ = v___x_2641_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_a_2636_);
v___x_2648_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v_a_2635_ = v_tail_2639_;
v_a_2636_ = v___x_2648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2652_, lean_object* v_k_2653_, lean_object* v_x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v_m_2658_; lean_object* v_a_2659_; uint8_t v___x_2660_; 
v___x_2656_ = lean_nat_add(v_x_2654_, v_x_2655_);
v___x_2657_ = lean_unsigned_to_nat(1u);
v_m_2658_ = lean_nat_shiftr(v___x_2656_, v___x_2657_);
lean_dec(v___x_2656_);
v_a_2659_ = lean_array_fget_borrowed(v_as_2652_, v_m_2658_);
v___x_2660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2659_, v_k_2653_);
if (v___x_2660_ == 0)
{
uint8_t v___x_2661_; 
lean_dec(v_x_2655_);
v___x_2661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2653_, v_a_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_m_2658_);
lean_dec(v_x_2654_);
lean_inc(v_a_2659_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_a_2659_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = lean_nat_dec_eq(v_m_2658_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = lean_nat_sub(v_m_2658_, v___x_2657_);
lean_dec(v_m_2658_);
v___x_2666_ = lean_nat_dec_lt(v___x_2665_, v_x_2654_);
if (v___x_2666_ == 0)
{
v_x_2655_ = v___x_2665_;
goto _start;
}
else
{
lean_object* v___x_2668_; 
lean_dec(v___x_2665_);
lean_dec(v_x_2654_);
v___x_2668_ = lean_box(0);
return v___x_2668_;
}
}
else
{
lean_object* v___x_2669_; 
lean_dec(v_m_2658_);
lean_dec(v_x_2654_);
v___x_2669_ = lean_box(0);
return v___x_2669_;
}
}
}
else
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
lean_dec(v_x_2654_);
v___x_2670_ = lean_nat_add(v_m_2658_, v___x_2657_);
lean_dec(v_m_2658_);
v___x_2671_ = lean_nat_dec_le(v___x_2670_, v_x_2655_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec(v___x_2670_);
lean_dec(v_x_2655_);
v___x_2672_ = lean_box(0);
return v___x_2672_;
}
else
{
v_x_2654_ = v___x_2670_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2674_, lean_object* v_k_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2674_, v_k_2675_, v_x_2676_, v_x_2677_);
lean_dec_ref(v_k_2675_);
lean_dec_ref(v_as_2674_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_env_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_env_2686_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2682_);
v___x_2687_ = lean_box(1);
v___x_2688_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2686_, v_tag_2679_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2689_; lean_object* v_toEnvExtension_2690_; lean_object* v_asyncMode_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2689_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2690_ = lean_ctor_get(v___x_2689_, 0);
v_asyncMode_2691_ = lean_ctor_get(v_toEnvExtension_2690_, 2);
v___x_2692_ = lean_box(0);
v___x_2693_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2687_, v___x_2689_, v_env_2686_, v_asyncMode_2691_, v___x_2692_);
v___x_2694_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2693_, v_tag_2679_);
lean_dec(v_tag_2679_);
lean_dec(v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
else
{
lean_object* v_val_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2724_; 
v_val_2696_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2698_ = v___x_2688_;
v_isShared_2699_ = v_isSharedCheck_2724_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_val_2696_);
lean_dec(v___x_2688_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2724_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2700_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2701_ = 0;
v___x_2702_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2687_, v___x_2700_, v_env_2686_, v_val_2696_, v___x_2701_);
lean_dec(v_val_2696_);
lean_dec_ref(v_env_2686_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_array_get_size(v___x_2702_);
v___x_2705_ = lean_nat_dec_lt(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_dec_ref(v___x_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_tag_2679_);
goto v___jp_2683_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_sub(v___x_2704_, v___x_2706_);
v___x_2708_ = lean_nat_dec_le(v___x_2703_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_dec(v___x_2707_);
lean_dec_ref(v___x_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_tag_2679_);
goto v___jp_2683_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_tag_2679_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2702_, v___x_2710_, v___x_2703_, v___x_2707_);
lean_dec_ref_known(v___x_2710_, 2);
lean_dec_ref(v___x_2702_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_del_object(v___x_2698_);
goto v___jp_2683_;
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2723_; 
v_val_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2723_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_val_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2723_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_snd_2716_; lean_object* v___x_2718_; 
v_snd_2716_ = lean_ctor_get(v_val_2712_, 1);
lean_inc(v_snd_2716_);
lean_dec(v_val_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v_snd_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_snd_2716_);
v___x_2718_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2718_);
v___x_2720_ = v___x_2698_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
}
v___jp_2683_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2725_, v___y_2726_);
lean_dec(v___y_2726_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2729_, size_t v_sz_2730_, size_t v_i_2731_, lean_object* v_b_2732_){
_start:
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_usize_dec_lt(v_i_2731_, v_sz_2730_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_b_2732_);
return v___x_2735_;
}
else
{
lean_object* v_a_2736_; lean_object* v_fst_2737_; lean_object* v_found_2738_; size_t v___x_2739_; size_t v___x_2740_; 
v_a_2736_ = lean_array_uget_borrowed(v_as_2729_, v_i_2731_);
v_fst_2737_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_fst_2737_);
v_found_2738_ = l_Lean_NameSet_insert(v_b_2732_, v_fst_2737_);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2731_, v___x_2739_);
v_i_2731_ = v___x_2740_;
v_b_2732_ = v_found_2738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2742_, lean_object* v_sz_2743_, lean_object* v_i_2744_, lean_object* v_b_2745_, lean_object* v___y_2746_){
_start:
{
size_t v_sz_boxed_2747_; size_t v_i_boxed_2748_; lean_object* v_res_2749_; 
v_sz_boxed_2747_ = lean_unbox_usize(v_sz_2743_);
lean_dec(v_sz_2743_);
v_i_boxed_2748_ = lean_unbox_usize(v_i_2744_);
lean_dec(v_i_2744_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2742_, v_sz_boxed_2747_, v_i_boxed_2748_, v_b_2745_);
lean_dec_ref(v_as_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2750_, size_t v_sz_2751_, size_t v_i_2752_, lean_object* v_b_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_lt(v_i_2752_, v_sz_2751_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_b_2753_);
return v___x_2758_;
}
else
{
lean_object* v_a_2759_; size_t v_sz_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
v_a_2759_ = lean_array_uget_borrowed(v_as_2750_, v_i_2752_);
v_sz_2760_ = lean_array_size(v_a_2759_);
v___x_2761_ = ((size_t)0ULL);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2759_, v_sz_2760_, v___x_2761_, v_b_2753_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; size_t v___x_2764_; size_t v___x_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = ((size_t)1ULL);
v___x_2765_ = lean_usize_add(v_i_2752_, v___x_2764_);
v_i_2752_ = v___x_2765_;
v_b_2753_ = v_a_2763_;
goto _start;
}
else
{
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2767_, lean_object* v_sz_2768_, lean_object* v_i_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
size_t v_sz_boxed_2774_; size_t v_i_boxed_2775_; lean_object* v_res_2776_; 
v_sz_boxed_2774_ = lean_unbox_usize(v_sz_2768_);
lean_dec(v_sz_2768_);
v_i_boxed_2775_ = lean_unbox_usize(v_i_2769_);
lean_dec(v_i_2769_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2767_, v_sz_boxed_2774_, v_i_boxed_2775_, v_b_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_as_2767_);
return v_res_2776_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2777_, lean_object* v_x1_2778_, lean_object* v_x2_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2780_ = l_Lean_Name_toString(v_x1_2778_, v___x_2777_);
v___x_2781_ = l_Lean_Name_toString(v_x2_2779_, v___x_2777_);
v___x_2782_ = lean_string_dec_lt(v___x_2780_, v___x_2781_);
lean_dec_ref(v___x_2781_);
lean_dec_ref(v___x_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2783_, lean_object* v_x1_2784_, lean_object* v_x2_2785_){
_start:
{
uint8_t v___x_7548__boxed_2786_; uint8_t v_res_2787_; lean_object* v_r_2788_; 
v___x_7548__boxed_2786_ = lean_unbox(v___x_2783_);
v_res_2787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_7548__boxed_2786_, v_x1_2784_, v_x2_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object* v_hi_2789_, lean_object* v_pivot_2790_, lean_object* v_as_2791_, lean_object* v_i_2792_, lean_object* v_k_2793_){
_start:
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_nat_dec_lt(v_k_2793_, v_hi_2789_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec(v_k_2793_);
lean_dec(v_pivot_2790_);
v___x_2795_ = lean_array_fswap(v_as_2791_, v_i_2792_, v_hi_2789_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_i_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2797_ = lean_array_fget_borrowed(v_as_2791_, v_k_2793_);
lean_inc(v___x_2797_);
v___x_2798_ = l_Lean_Name_toString(v___x_2797_, v___x_2794_);
lean_inc(v_pivot_2790_);
v___x_2799_ = l_Lean_Name_toString(v_pivot_2790_, v___x_2794_);
v___x_2800_ = lean_string_dec_lt(v___x_2798_, v___x_2799_);
lean_dec_ref(v___x_2799_);
lean_dec_ref(v___x_2798_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_nat_add(v_k_2793_, v___x_2801_);
lean_dec(v_k_2793_);
v_k_2793_ = v___x_2802_;
goto _start;
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2804_ = lean_array_fswap(v_as_2791_, v_i_2792_, v_k_2793_);
v___x_2805_ = lean_unsigned_to_nat(1u);
v___x_2806_ = lean_nat_add(v_i_2792_, v___x_2805_);
lean_dec(v_i_2792_);
v___x_2807_ = lean_nat_add(v_k_2793_, v___x_2805_);
lean_dec(v_k_2793_);
v_as_2791_ = v___x_2804_;
v_i_2792_ = v___x_2806_;
v_k_2793_ = v___x_2807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_hi_2809_, lean_object* v_pivot_2810_, lean_object* v_as_2811_, lean_object* v_i_2812_, lean_object* v_k_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2809_, v_pivot_2810_, v_as_2811_, v_i_2812_, v_k_2813_);
lean_dec(v_hi_2809_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_n_2815_, lean_object* v_as_2816_, lean_object* v_lo_2817_, lean_object* v_hi_2818_){
_start:
{
lean_object* v___y_2820_; uint8_t v___x_2830_; 
v___x_2830_ = lean_nat_dec_lt(v_lo_2817_, v_hi_2818_);
if (v___x_2830_ == 0)
{
lean_dec(v_lo_2817_);
return v_as_2816_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v_mid_2833_; lean_object* v___y_2835_; lean_object* v___y_2841_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2831_ = lean_nat_add(v_lo_2817_, v_hi_2818_);
v___x_2832_ = lean_unsigned_to_nat(1u);
v_mid_2833_ = lean_nat_shiftr(v___x_2831_, v___x_2832_);
lean_dec(v___x_2831_);
v___x_2846_ = lean_array_fget_borrowed(v_as_2816_, v_mid_2833_);
v___x_2847_ = lean_array_fget_borrowed(v_as_2816_, v_lo_2817_);
lean_inc(v___x_2847_);
lean_inc(v___x_2846_);
v___x_2848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2830_, v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
v___y_2841_ = v_as_2816_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_array_fswap(v_as_2816_, v_lo_2817_, v_mid_2833_);
v___y_2841_ = v___x_2849_;
goto v___jp_2840_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = lean_array_fget_borrowed(v___y_2835_, v_mid_2833_);
v___x_2837_ = lean_array_fget_borrowed(v___y_2835_, v_hi_2818_);
lean_inc(v___x_2837_);
lean_inc(v___x_2836_);
v___x_2838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2830_, v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_dec(v_mid_2833_);
v___y_2820_ = v___y_2835_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_array_fswap(v___y_2835_, v_mid_2833_, v_hi_2818_);
lean_dec(v_mid_2833_);
v___y_2820_ = v___x_2839_;
goto v___jp_2819_;
}
}
v___jp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_array_fget_borrowed(v___y_2841_, v_hi_2818_);
v___x_2843_ = lean_array_fget_borrowed(v___y_2841_, v_lo_2817_);
lean_inc(v___x_2843_);
lean_inc(v___x_2842_);
v___x_2844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2830_, v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
v___y_2835_ = v___y_2841_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_array_fswap(v___y_2841_, v_lo_2817_, v_hi_2818_);
v___y_2835_ = v___x_2845_;
goto v___jp_2834_;
}
}
}
v___jp_2819_:
{
lean_object* v_pivot_2821_; lean_object* v___x_2822_; lean_object* v_fst_2823_; lean_object* v_snd_2824_; uint8_t v___x_2825_; 
v_pivot_2821_ = lean_array_fget(v___y_2820_, v_hi_2818_);
lean_inc_n(v_lo_2817_, 2);
v___x_2822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2818_, v_pivot_2821_, v___y_2820_, v_lo_2817_, v_lo_2817_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_fst_2823_);
v_snd_2824_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_snd_2824_);
lean_dec_ref(v___x_2822_);
v___x_2825_ = lean_nat_dec_le(v_hi_2818_, v_fst_2823_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2815_, v_snd_2824_, v_lo_2817_, v_fst_2823_);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_fst_2823_, v___x_2827_);
lean_dec(v_fst_2823_);
v_as_2816_ = v___x_2826_;
v_lo_2817_ = v___x_2828_;
goto _start;
}
else
{
lean_dec(v_fst_2823_);
lean_dec(v_lo_2817_);
return v_snd_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_n_2850_, lean_object* v_as_2851_, lean_object* v_lo_2852_, lean_object* v_hi_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2850_, v_as_2851_, v_lo_2852_, v_hi_2853_);
lean_dec(v_hi_2853_);
lean_dec(v_n_2850_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2855_, lean_object* v_x_2856_){
_start:
{
if (lean_obj_tag(v_x_2856_) == 0)
{
lean_object* v_k_2858_; lean_object* v_l_2859_; lean_object* v_r_2860_; lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_k_2858_ = lean_ctor_get(v_x_2856_, 1);
lean_inc(v_k_2858_);
v_l_2859_ = lean_ctor_get(v_x_2856_, 3);
lean_inc(v_l_2859_);
v_r_2860_ = lean_ctor_get(v_x_2856_, 4);
lean_inc(v_r_2860_);
lean_dec_ref_known(v_x_2856_, 5);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2855_, v_l_2859_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
v_a_2863_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_a_2863_);
lean_dec(v_a_2862_);
v___x_2864_ = l_Lean_NameSet_insert(v_a_2863_, v_k_2858_);
v_init_2855_ = v___x_2864_;
v_x_2856_ = v_r_2860_;
goto _start;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_init_2855_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2868_, lean_object* v_x_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2868_, v_x_2869_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v_k_2874_; lean_object* v_l_2875_; lean_object* v_r_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_k_2874_ = lean_ctor_get(v_x_2873_, 1);
lean_inc(v_k_2874_);
v_l_2875_ = lean_ctor_get(v_x_2873_, 3);
lean_inc(v_l_2875_);
v_r_2876_ = lean_ctor_get(v_x_2873_, 4);
lean_inc(v_r_2876_);
lean_dec_ref_known(v_x_2873_, 5);
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2872_, v_l_2875_);
v___x_2878_ = lean_array_push(v___x_2877_, v_k_2874_);
v_init_2872_ = v___x_2878_;
v_x_2873_ = v_r_2876_;
goto _start;
}
else
{
return v_init_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___y_2884_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___x_2910_; lean_object* v_env_2911_; lean_object* v___x_2912_; lean_object* v_toEnvExtension_2913_; lean_object* v_asyncMode_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_found_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v_a_2921_; lean_object* v_a_2923_; lean_object* v_a_2940_; 
v___x_2910_ = lean_st_ref_get(v___y_2881_);
v_env_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_ref_n(v_env_2911_, 2);
lean_dec(v___x_2910_);
v___x_2912_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2913_ = lean_ctor_get(v___x_2912_, 0);
v_asyncMode_2914_ = lean_ctor_get(v_toEnvExtension_2913_, 2);
v___x_2915_ = lean_box(1);
v___x_2916_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
v_found_2917_ = l_Lean_NameSet_empty;
v___x_2918_ = lean_box(0);
v___x_2919_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2915_, v___x_2912_, v_env_2911_, v_asyncMode_2914_, v___x_2918_);
v___x_2920_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2917_, v___x_2919_);
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v_a_2940_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_a_2940_);
lean_dec(v_a_2921_);
v_a_2923_ = v_a_2940_;
goto v___jp_2922_;
v___jp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_array_to_list(v___y_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
v___jp_2887_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2888_, v___y_2890_, v___y_2889_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec(v___y_2888_);
v___y_2884_ = v___x_2892_;
goto v___jp_2883_;
}
v___jp_2893_:
{
uint8_t v___x_2898_; 
v___x_2898_ = lean_nat_dec_le(v___y_2897_, v___y_2895_);
if (v___x_2898_ == 0)
{
lean_dec(v___y_2895_);
lean_inc(v___y_2897_);
v___y_2888_ = v___y_2894_;
v___y_2889_ = v___y_2897_;
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2897_;
goto v___jp_2887_;
}
else
{
v___y_2888_ = v___y_2894_;
v___y_2889_ = v___y_2897_;
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2895_;
goto v___jp_2887_;
}
}
v___jp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2902_ = lean_mk_empty_array_with_capacity(v___y_2901_);
lean_dec(v___y_2901_);
v___x_2903_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2902_, v___y_2900_);
v___x_2904_ = lean_array_get_size(v___x_2903_);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_nat_dec_eq(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_nat_sub(v___x_2904_, v___x_2907_);
v___x_2909_ = lean_nat_dec_le(v___x_2905_, v___x_2908_);
if (v___x_2909_ == 0)
{
lean_inc(v___x_2908_);
v___y_2894_ = v___x_2904_;
v___y_2895_ = v___x_2908_;
v___y_2896_ = v___x_2903_;
v___y_2897_ = v___x_2908_;
goto v___jp_2893_;
}
else
{
v___y_2894_ = v___x_2904_;
v___y_2895_ = v___x_2908_;
v___y_2896_ = v___x_2903_;
v___y_2897_ = v___x_2905_;
goto v___jp_2893_;
}
}
else
{
v___y_2884_ = v___x_2903_;
goto v___jp_2883_;
}
}
v___jp_2922_:
{
lean_object* v___x_2924_; lean_object* v_importedEntries_2925_; size_t v_sz_2926_; size_t v___x_2927_; lean_object* v___x_2928_; 
v___x_2924_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2916_, v_toEnvExtension_2913_, v_env_2911_, v_asyncMode_2914_, v___x_2918_);
v_importedEntries_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc_ref(v_importedEntries_2925_);
lean_dec(v___x_2924_);
v_sz_2926_ = lean_array_size(v_importedEntries_2925_);
v___x_2927_ = ((size_t)0ULL);
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2925_, v_sz_2926_, v___x_2927_, v_a_2923_, v___y_2880_, v___y_2881_);
lean_dec_ref(v_importedEntries_2925_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
if (lean_obj_tag(v_a_2929_) == 0)
{
lean_object* v_size_2930_; 
v_size_2930_ = lean_ctor_get(v_a_2929_, 0);
lean_inc(v_size_2930_);
v___y_2900_ = v_a_2929_;
v___y_2901_ = v_size_2930_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_unsigned_to_nat(0u);
v___y_2900_ = v_a_2929_;
v___y_2901_ = v___x_2931_;
goto v___jp_2899_;
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2928_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2928_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2944_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2956_ = l_Lean_stringToMessageData(v___x_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2963_ = l_Lean_MessageData_ofFormat(v___x_2962_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2968_ = l_Lean_MessageData_ofFormat(v___x_2967_);
return v___x_2968_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2971_ = l_Lean_stringToMessageData(v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2972_, lean_object* v_as_2973_, size_t v_sz_2974_, size_t v_i_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_a_2981_; uint8_t v___x_2985_; 
v___x_2985_ = lean_usize_dec_lt(v_i_2975_, v_sz_2974_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v_decl_2972_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2976_);
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2987_ = lean_array_uget_borrowed(v_as_2973_, v_i_2975_);
v___x_2988_ = l_Lean_TSyntax_getId(v_a_2987_);
lean_inc(v___x_2988_);
v___x_2989_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2988_, v___y_2978_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = lean_box(0);
if (lean_obj_tag(v_a_2990_) == 1)
{
lean_object* v___x_2992_; lean_object* v_env_2993_; lean_object* v_nextMacroScope_2994_; lean_object* v_ngen_2995_; lean_object* v_auxDeclNGen_2996_; lean_object* v_traceState_2997_; lean_object* v_messages_2998_; lean_object* v_infoState_2999_; lean_object* v_snapshotTasks_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref_known(v_a_2990_, 1);
v___x_2992_ = lean_st_ref_take(v___y_2978_);
v_env_2993_ = lean_ctor_get(v___x_2992_, 0);
v_nextMacroScope_2994_ = lean_ctor_get(v___x_2992_, 1);
v_ngen_2995_ = lean_ctor_get(v___x_2992_, 2);
v_auxDeclNGen_2996_ = lean_ctor_get(v___x_2992_, 3);
v_traceState_2997_ = lean_ctor_get(v___x_2992_, 4);
v_messages_2998_ = lean_ctor_get(v___x_2992_, 6);
v_infoState_2999_ = lean_ctor_get(v___x_2992_, 7);
v_snapshotTasks_3000_ = lean_ctor_get(v___x_2992_, 8);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_2992_, 5);
lean_dec(v_unused_3016_);
v___x_3002_ = v___x_2992_;
v_isShared_3003_ = v_isSharedCheck_3015_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_snapshotTasks_3000_);
lean_inc(v_infoState_2999_);
lean_inc(v_messages_2998_);
lean_inc(v_traceState_2997_);
lean_inc(v_auxDeclNGen_2996_);
lean_inc(v_ngen_2995_);
lean_inc(v_nextMacroScope_2994_);
lean_inc(v_env_2993_);
lean_dec(v___x_2992_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3015_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v_toEnvExtension_3005_; lean_object* v_asyncMode_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3004_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3005_ = lean_ctor_get(v___x_3004_, 0);
v_asyncMode_3006_ = lean_ctor_get(v_toEnvExtension_3005_, 2);
v___x_3007_ = lean_box(0);
lean_inc(v_decl_2972_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_decl_2972_);
lean_ctor_set(v___x_3008_, 1, v___x_2988_);
v___x_3009_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3004_, v_env_2993_, v___x_3008_, v_asyncMode_3006_, v___x_3007_);
v___x_3010_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 5, v___x_3010_);
lean_ctor_set(v___x_3002_, 0, v___x_3009_);
v___x_3012_ = v___x_3002_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_nextMacroScope_2994_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_ngen_2995_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_auxDeclNGen_2996_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_traceState_2997_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3014_, 6, v_messages_2998_);
lean_ctor_set(v_reuseFailAlloc_3014_, 7, v_infoState_2999_);
lean_ctor_set(v_reuseFailAlloc_3014_, 8, v_snapshotTasks_3000_);
v___x_3012_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_st_ref_set(v___y_2978_, v___x_3012_);
v_a_2981_ = v___x_2991_;
goto v___jp_2980_;
}
}
}
else
{
lean_object* v___x_3017_; 
lean_dec(v_a_2990_);
v___x_3017_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___y_3020_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = l_List_lengthTR___redArg(v_a_3018_);
v___x_3034_ = lean_nat_dec_eq(v___x_3033_, v___x_3032_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = lean_unsigned_to_nat(1u);
v___x_3036_ = lean_nat_dec_eq(v___x_3033_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(10u);
v___x_3038_ = lean_nat_dec_lt(v___x_3033_, v___x_3037_);
lean_dec(v___x_3033_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_3018_);
v___x_3041_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_3018_, v_a_3018_, v___x_3037_, v___x_3040_);
lean_dec(v_a_3018_);
v___x_3042_ = lean_box(0);
v___x_3043_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_3041_, v___x_3042_);
v___x_3044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3045_ = l_Lean_MessageData_joinSep(v___x_3043_, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3039_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___y_3020_ = v___x_3048_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3050_ = lean_box(0);
v___x_3051_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3018_, v___x_3050_);
v___x_3052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3053_ = l_Lean_MessageData_joinSep(v___x_3051_, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3049_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___y_3020_ = v___x_3054_;
goto v___jp_3019_;
}
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec(v___x_3033_);
v___x_3055_ = lean_box(0);
v___x_3056_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3018_, v___x_3055_);
v___x_3057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3058_ = l_Lean_MessageData_joinSep(v___x_3056_, v___x_3057_);
v___y_3020_ = v___x_3058_;
goto v___jp_3019_;
}
}
else
{
lean_object* v___x_3059_; 
lean_dec(v___x_3033_);
lean_dec(v_a_3018_);
v___x_3059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_3020_ = v___x_3059_;
goto v___jp_3019_;
}
v___jp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3021_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___y_3020_);
v___x_3023_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_3026_ = l_Lean_MessageData_ofName(v___x_2988_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v___x_3024_);
v___x_3031_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_a_2987_, v___x_3030_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_dec_ref_known(v___x_3031_, 1);
v_a_2981_ = v___x_2991_;
goto v___jp_2980_;
}
else
{
lean_dec(v_decl_2972_);
return v___x_3031_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v___x_2988_);
lean_dec(v_decl_2972_);
v_a_3060_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3017_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3017_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v___x_2988_);
lean_dec(v_decl_2972_);
v_a_3068_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2989_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2989_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
v___jp_2980_:
{
size_t v___x_2982_; size_t v___x_2983_; 
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2975_, v___x_2982_);
v_i_2975_ = v___x_2983_;
v_b_2976_ = v_a_2981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_3076_, lean_object* v_as_3077_, lean_object* v_sz_3078_, lean_object* v_i_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
size_t v_sz_boxed_3084_; size_t v_i_boxed_3085_; lean_object* v_res_3086_; 
v_sz_boxed_3084_ = lean_unbox_usize(v_sz_3078_);
lean_dec(v_sz_3078_);
v_i_boxed_3085_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3076_, v_as_3077_, v_sz_boxed_3084_, v_i_boxed_3085_, v_b_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_as_3077_);
return v_res_3086_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3089_ = l_Lean_stringToMessageData(v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_3090_, lean_object* v___x_3091_, lean_object* v___x_3092_, lean_object* v_name_3093_, lean_object* v_decl_3094_, lean_object* v_stx_3095_, uint8_t v_kind_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; uint8_t v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = 0;
v___x_3162_ = l_Lean_instBEqAttributeKind_beq(v_kind_3096_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec(v_stx_3095_);
lean_dec(v_decl_3094_);
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v___x_3090_);
v___x_3163_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_3093_, v_kind_3096_, v___y_3097_, v___y_3098_);
return v___x_3163_;
}
else
{
goto v___jp_3134_;
}
v___jp_3100_:
{
lean_object* v___x_3104_; size_t v_sz_3105_; size_t v___x_3106_; lean_object* v___x_3107_; 
v___x_3104_ = lean_box(0);
v_sz_3105_ = lean_array_size(v___y_3101_);
v___x_3106_ = ((size_t)0ULL);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3094_, v___y_3101_, v_sz_3105_, v___x_3106_, v___x_3104_, v___y_3102_, v___y_3103_);
lean_dec_ref(v___y_3101_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; 
v_unused_3115_ = lean_ctor_get(v___x_3107_, 0);
lean_dec(v_unused_3115_);
v___x_3109_ = v___x_3107_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v___x_3107_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3104_);
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3104_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
return v___x_3107_;
}
}
v___jp_3116_:
{
lean_object* v___x_3120_; lean_object* v_env_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_st_ref_get(v___y_3119_);
v_env_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_env_3121_);
lean_dec(v___x_3120_);
lean_inc(v_decl_3094_);
v___x_3122_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3121_, v_decl_3094_);
if (lean_obj_tag(v___x_3122_) == 1)
{
lean_object* v_val_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec_ref(v___y_3117_);
v_val_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3125_ = 0;
v___x_3126_ = l_Lean_MessageData_ofConstName(v_decl_3094_, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3124_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_MessageData_ofConstName(v_val_3123_, v___x_3125_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3124_);
v___x_3133_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3095_, v___x_3132_, v___y_3118_, v___y_3119_);
lean_dec(v_stx_3095_);
return v___x_3133_;
}
else
{
lean_dec(v___x_3122_);
lean_dec(v_stx_3095_);
v___y_3101_ = v___y_3117_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
goto v___jp_3100_;
}
}
v___jp_3134_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3135_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_3136_ = l_Lean_Name_mkStr4(v___x_3090_, v___x_3091_, v___x_3135_, v___x_3092_);
lean_inc(v_stx_3095_);
v___x_3137_ = l_Lean_Syntax_isOfKind(v_stx_3095_, v___x_3136_);
lean_dec(v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_stx_3095_);
lean_dec(v_decl_3094_);
v___x_3138_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3139_ = l_Lean_MessageData_ofName(v_name_3093_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_3142_, v___y_3097_, v___y_3098_);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; lean_object* v_env_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v_tags_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_name_3093_);
v___x_3144_ = lean_st_ref_get(v___y_3098_);
v_env_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc_ref(v_env_3145_);
lean_dec(v___x_3144_);
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = l_Lean_Syntax_getArg(v_stx_3095_, v___x_3146_);
v_tags_3148_ = l_Lean_Syntax_getArgs(v___x_3147_);
lean_dec(v___x_3147_);
v___x_3149_ = 0;
lean_inc(v_decl_3094_);
v___x_3150_ = l_Lean_Environment_find_x3f(v_env_3145_, v_decl_3094_, v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
v___y_3117_ = v_tags_3148_;
v___y_3118_ = v___y_3097_;
v___y_3119_ = v___y_3098_;
goto v___jp_3116_;
}
else
{
lean_dec_ref_known(v___x_3150_, 1);
if (v___x_3137_ == 0)
{
v___y_3117_ = v_tags_3148_;
v___y_3118_ = v___y_3097_;
v___y_3119_ = v___y_3098_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3151_; lean_object* v_env_3152_; uint8_t v___x_3153_; uint8_t v___x_3154_; 
v___x_3151_ = lean_st_ref_get(v___y_3098_);
v_env_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_ref(v_env_3152_);
lean_dec(v___x_3151_);
v___x_3153_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_3152_, v_decl_3094_);
v___x_3154_ = lean_bool_not(v___x_3153_);
if (v___x_3154_ == 0)
{
v___y_3117_ = v_tags_3148_;
v___y_3118_ = v___y_3097_;
v___y_3119_ = v___y_3098_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec_ref(v_tags_3148_);
v___x_3155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3156_ = l_Lean_MessageData_ofConstName(v_decl_3094_, v___x_3149_);
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3095_, v___x_3159_, v___y_3097_, v___y_3098_);
lean_dec(v_stx_3095_);
return v___x_3160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_3164_, lean_object* v___x_3165_, lean_object* v___x_3166_, lean_object* v_name_3167_, lean_object* v_decl_3168_, lean_object* v_stx_3169_, lean_object* v_kind_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v_kind_boxed_3174_; lean_object* v_res_3175_; 
v_kind_boxed_3174_ = lean_unbox(v_kind_3170_);
v_res_3175_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_3164_, v___x_3165_, v___x_3166_, v_name_3167_, v_decl_3168_, v_stx_3169_, v_kind_boxed_3174_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3210_ = l_Lean_registerBuiltinAttribute(v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_3213_, v___y_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_3223_, lean_object* v_k_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3223_, v_k_3224_, v_x_3225_, v_x_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_3229_, lean_object* v_k_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_3229_, v_k_3230_, v_x_3231_, v_x_3232_, v_x_3233_);
lean_dec_ref(v_k_3230_);
lean_dec_ref(v_as_3229_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_3235_, size_t v_sz_3236_, size_t v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_3235_, v_sz_3236_, v_i_3237_, v_b_3238_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_3243_, lean_object* v_sz_3244_, lean_object* v_i_3245_, lean_object* v_b_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
size_t v_sz_boxed_3250_; size_t v_i_boxed_3251_; lean_object* v_res_3252_; 
v_sz_boxed_3250_ = lean_unbox_usize(v_sz_3244_);
lean_dec(v_sz_3244_);
v_i_boxed_3251_ = lean_unbox_usize(v_i_3245_);
lean_dec(v_i_3245_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_3243_, v_sz_boxed_3250_, v_i_boxed_3251_, v_b_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v_as_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_3253_, lean_object* v_t_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_3253_, v_t_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_3256_, lean_object* v_as_3257_, lean_object* v_lo_3258_, lean_object* v_hi_3259_, lean_object* v_w_3260_, lean_object* v_hlo_3261_, lean_object* v_hhi_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_3256_, v_as_3257_, v_lo_3258_, v_hi_3259_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_3264_, lean_object* v_as_3265_, lean_object* v_lo_3266_, lean_object* v_hi_3267_, lean_object* v_w_3268_, lean_object* v_hlo_3269_, lean_object* v_hhi_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_3264_, v_as_3265_, v_lo_3266_, v_hi_3267_, v_w_3268_, v_hlo_3269_, v_hhi_3270_);
lean_dec(v_hi_3267_);
lean_dec(v_n_3264_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_3272_, lean_object* v_x_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_3272_, v_x_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_3278_, v_x_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object* v_n_3284_, lean_object* v_lo_3285_, lean_object* v_hi_3286_, lean_object* v_hhi_3287_, lean_object* v_pivot_3288_, lean_object* v_as_3289_, lean_object* v_i_3290_, lean_object* v_k_3291_, lean_object* v_ilo_3292_, lean_object* v_ik_3293_, lean_object* v_w_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_3286_, v_pivot_3288_, v_as_3289_, v_i_3290_, v_k_3291_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object* v_n_3296_, lean_object* v_lo_3297_, lean_object* v_hi_3298_, lean_object* v_hhi_3299_, lean_object* v_pivot_3300_, lean_object* v_as_3301_, lean_object* v_i_3302_, lean_object* v_k_3303_, lean_object* v_ilo_3304_, lean_object* v_ik_3305_, lean_object* v_w_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(v_n_3296_, v_lo_3297_, v_hi_3298_, v_hhi_3299_, v_pivot_3300_, v_as_3301_, v_i_3302_, v_k_3303_, v_ilo_3304_, v_ik_3305_, v_w_3306_);
lean_dec(v_hi_3298_);
lean_dec(v_lo_3297_);
lean_dec(v_n_3296_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_fst_3312_ = lean_ctor_get(v_x_3311_, 0);
lean_inc(v_fst_3312_);
v_snd_3313_ = lean_ctor_get(v_x_3311_, 1);
lean_inc(v_snd_3313_);
lean_dec_ref(v_x_3311_);
v___x_3314_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3315_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3310_, v_fst_3312_, v___x_3314_);
v___x_3316_ = lean_array_push(v___x_3315_, v_snd_3313_);
v___x_3317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3312_, v___x_3316_, v_es_3310_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v_k_3320_; lean_object* v_v_3321_; lean_object* v_l_3322_; lean_object* v_r_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_k_3320_ = lean_ctor_get(v_x_3319_, 1);
v_v_3321_ = lean_ctor_get(v_x_3319_, 2);
v_l_3322_ = lean_ctor_get(v_x_3319_, 3);
v_r_3323_ = lean_ctor_get(v_x_3319_, 4);
v___x_3324_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3318_, v_l_3322_);
lean_inc(v_v_3321_);
lean_inc(v_k_3320_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_k_3320_);
lean_ctor_set(v___x_3325_, 1, v_v_3321_);
v___x_3326_ = lean_array_push(v___x_3324_, v___x_3325_);
v_init_3318_ = v___x_3326_;
v_x_3319_ = v_r_3323_;
goto _start;
}
else
{
return v_init_3318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3328_, v_x_3329_);
lean_dec(v_x_3329_);
return v_res_3330_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3331_, lean_object* v_x2_3332_){
_start:
{
lean_object* v_fst_3333_; lean_object* v_fst_3334_; uint8_t v___x_3335_; 
v_fst_3333_ = lean_ctor_get(v_x1_3331_, 0);
v_fst_3334_ = lean_ctor_get(v_x2_3332_, 0);
v___x_3335_ = l_Lean_Name_quickLt(v_fst_3333_, v_fst_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3336_, lean_object* v_x2_3337_){
_start:
{
uint8_t v_res_3338_; lean_object* v_r_3339_; 
v_res_3338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3336_, v_x2_3337_);
lean_dec_ref(v_x2_3337_);
lean_dec_ref(v_x1_3336_);
v_r_3339_ = lean_box(v_res_3338_);
return v_r_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3340_, lean_object* v_pivot_3341_, lean_object* v_as_3342_, lean_object* v_i_3343_, lean_object* v_k_3344_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_nat_dec_lt(v_k_3344_, v_hi_3340_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec(v_k_3344_);
v___x_3346_ = lean_array_fswap(v_as_3342_, v_i_3343_, v_hi_3340_);
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_i_3343_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v___x_3348_; lean_object* v_fst_3349_; lean_object* v_fst_3350_; uint8_t v___x_3351_; 
v___x_3348_ = lean_array_fget_borrowed(v_as_3342_, v_k_3344_);
v_fst_3349_ = lean_ctor_get(v___x_3348_, 0);
v_fst_3350_ = lean_ctor_get(v_pivot_3341_, 0);
v___x_3351_ = l_Lean_Name_quickLt(v_fst_3349_, v_fst_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_unsigned_to_nat(1u);
v___x_3353_ = lean_nat_add(v_k_3344_, v___x_3352_);
lean_dec(v_k_3344_);
v_k_3344_ = v___x_3353_;
goto _start;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3355_ = lean_array_fswap(v_as_3342_, v_i_3343_, v_k_3344_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_add(v_i_3343_, v___x_3356_);
lean_dec(v_i_3343_);
v___x_3358_ = lean_nat_add(v_k_3344_, v___x_3356_);
lean_dec(v_k_3344_);
v_as_3342_ = v___x_3355_;
v_i_3343_ = v___x_3357_;
v_k_3344_ = v___x_3358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3360_, lean_object* v_pivot_3361_, lean_object* v_as_3362_, lean_object* v_i_3363_, lean_object* v_k_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3360_, v_pivot_3361_, v_as_3362_, v_i_3363_, v_k_3364_);
lean_dec_ref(v_pivot_3361_);
lean_dec(v_hi_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3366_, lean_object* v_as_3367_, lean_object* v_lo_3368_, lean_object* v_hi_3369_){
_start:
{
lean_object* v___y_3371_; uint8_t v___x_3381_; 
v___x_3381_ = lean_nat_dec_lt(v_lo_3368_, v_hi_3369_);
if (v___x_3381_ == 0)
{
lean_dec(v_lo_3368_);
return v_as_3367_;
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v_mid_3384_; lean_object* v___y_3386_; lean_object* v___y_3392_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3382_ = lean_nat_add(v_lo_3368_, v_hi_3369_);
v___x_3383_ = lean_unsigned_to_nat(1u);
v_mid_3384_ = lean_nat_shiftr(v___x_3382_, v___x_3383_);
lean_dec(v___x_3382_);
v___x_3397_ = lean_array_fget_borrowed(v_as_3367_, v_mid_3384_);
v___x_3398_ = lean_array_fget_borrowed(v_as_3367_, v_lo_3368_);
v___x_3399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
v___y_3392_ = v_as_3367_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_array_fswap(v_as_3367_, v_lo_3368_, v_mid_3384_);
v___y_3392_ = v___x_3400_;
goto v___jp_3391_;
}
v___jp_3385_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3387_ = lean_array_fget_borrowed(v___y_3386_, v_mid_3384_);
v___x_3388_ = lean_array_fget_borrowed(v___y_3386_, v_hi_3369_);
v___x_3389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3387_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_dec(v_mid_3384_);
v___y_3371_ = v___y_3386_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_array_fswap(v___y_3386_, v_mid_3384_, v_hi_3369_);
lean_dec(v_mid_3384_);
v___y_3371_ = v___x_3390_;
goto v___jp_3370_;
}
}
v___jp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = lean_array_fget_borrowed(v___y_3392_, v_hi_3369_);
v___x_3394_ = lean_array_fget_borrowed(v___y_3392_, v_lo_3368_);
v___x_3395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
v___y_3386_ = v___y_3392_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_array_fswap(v___y_3392_, v_lo_3368_, v_hi_3369_);
v___y_3386_ = v___x_3396_;
goto v___jp_3385_;
}
}
}
v___jp_3370_:
{
lean_object* v_pivot_3372_; lean_object* v___x_3373_; lean_object* v_fst_3374_; lean_object* v_snd_3375_; uint8_t v___x_3376_; 
v_pivot_3372_ = lean_array_fget(v___y_3371_, v_hi_3369_);
lean_inc_n(v_lo_3368_, 2);
v___x_3373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3369_, v_pivot_3372_, v___y_3371_, v_lo_3368_, v_lo_3368_);
lean_dec(v_pivot_3372_);
v_fst_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_fst_3374_);
v_snd_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc(v_snd_3375_);
lean_dec_ref(v___x_3373_);
v___x_3376_ = lean_nat_dec_le(v_hi_3369_, v_fst_3374_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3366_, v_snd_3375_, v_lo_3368_, v_fst_3374_);
v___x_3378_ = lean_unsigned_to_nat(1u);
v___x_3379_ = lean_nat_add(v_fst_3374_, v___x_3378_);
lean_dec(v_fst_3374_);
v_as_3367_ = v___x_3377_;
v_lo_3368_ = v___x_3379_;
goto _start;
}
else
{
lean_dec(v_fst_3374_);
lean_dec(v_lo_3368_);
return v_snd_3375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3401_, lean_object* v_as_3402_, lean_object* v_lo_3403_, lean_object* v_hi_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3401_, v_as_3402_, v_lo_3403_, v_hi_3404_);
lean_dec(v_hi_3404_);
lean_dec(v_n_3401_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3408_, lean_object* v_s_3409_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; uint8_t v___x_3419_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3411_, v_s_3409_);
v___x_3413_ = lean_array_get_size(v___x_3412_);
v___x_3419_ = lean_nat_dec_eq(v___x_3413_, v___x_3410_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___y_3423_; uint8_t v___x_3425_; 
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_sub(v___x_3413_, v___x_3420_);
v___x_3425_ = lean_nat_dec_le(v___x_3410_, v___x_3421_);
if (v___x_3425_ == 0)
{
lean_inc(v___x_3421_);
v___y_3423_ = v___x_3421_;
goto v___jp_3422_;
}
else
{
v___y_3423_ = v___x_3410_;
goto v___jp_3422_;
}
v___jp_3422_:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_nat_dec_le(v___y_3423_, v___x_3421_);
if (v___x_3424_ == 0)
{
lean_dec(v___x_3421_);
lean_inc(v___y_3423_);
v___y_3415_ = v___y_3423_;
v___y_3416_ = v___y_3423_;
goto v___jp_3414_;
}
else
{
v___y_3415_ = v___y_3423_;
v___y_3416_ = v___x_3421_;
goto v___jp_3414_;
}
}
}
else
{
lean_object* v___x_3426_; 
lean_inc_ref_n(v___x_3412_, 2);
v___x_3426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3412_);
lean_ctor_set(v___x_3426_, 1, v___x_3412_);
lean_ctor_set(v___x_3426_, 2, v___x_3412_);
return v___x_3426_;
}
v___jp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3413_, v___x_3412_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_inc_ref_n(v___x_3417_, 2);
v___x_3418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_ctor_set(v___x_3418_, 2, v___x_3417_);
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3427_, lean_object* v_s_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3427_, v_s_3428_);
lean_dec(v_s_3428_);
lean_dec_ref(v_x_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3432_, v_es_3430_);
v___x_3434_ = lean_array_get_size(v___x_3433_);
v___x_3435_ = lean_nat_dec_eq(v___x_3434_, v___x_3431_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___y_3439_; uint8_t v___x_3443_; 
v___x_3436_ = lean_unsigned_to_nat(1u);
v___x_3437_ = lean_nat_sub(v___x_3434_, v___x_3436_);
v___x_3443_ = lean_nat_dec_le(v___x_3431_, v___x_3437_);
if (v___x_3443_ == 0)
{
lean_inc(v___x_3437_);
v___y_3439_ = v___x_3437_;
goto v___jp_3438_;
}
else
{
v___y_3439_ = v___x_3431_;
goto v___jp_3438_;
}
v___jp_3438_:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_nat_dec_le(v___y_3439_, v___x_3437_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec(v___x_3437_);
lean_inc(v___y_3439_);
v___x_3441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3434_, v___x_3433_, v___y_3439_, v___y_3439_);
lean_dec(v___y_3439_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3434_, v___x_3433_, v___y_3439_, v___x_3437_);
lean_dec(v___x_3437_);
return v___x_3442_;
}
}
}
else
{
return v___x_3433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3444_);
lean_dec(v_es_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3446_, lean_object* v_x_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3446_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3451_, lean_object* v_x_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3451_, v_x_3452_, v___y_3453_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v_x_3452_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3482_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3485_, lean_object* v_t_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3485_, v_t_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3488_, lean_object* v_t_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3488_, v_t_3489_);
lean_dec(v_t_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3491_, lean_object* v_as_3492_, lean_object* v_lo_3493_, lean_object* v_hi_3494_, lean_object* v_w_3495_, lean_object* v_hlo_3496_, lean_object* v_hhi_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3491_, v_as_3492_, v_lo_3493_, v_hi_3494_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3499_, lean_object* v_as_3500_, lean_object* v_lo_3501_, lean_object* v_hi_3502_, lean_object* v_w_3503_, lean_object* v_hlo_3504_, lean_object* v_hhi_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3499_, v_as_3500_, v_lo_3501_, v_hi_3502_, v_w_3503_, v_hlo_3504_, v_hhi_3505_);
lean_dec(v_hi_3502_);
lean_dec(v_n_3499_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3507_, lean_object* v_lo_3508_, lean_object* v_hi_3509_, lean_object* v_hhi_3510_, lean_object* v_pivot_3511_, lean_object* v_as_3512_, lean_object* v_i_3513_, lean_object* v_k_3514_, lean_object* v_ilo_3515_, lean_object* v_ik_3516_, lean_object* v_w_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3509_, v_pivot_3511_, v_as_3512_, v_i_3513_, v_k_3514_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3519_, lean_object* v_lo_3520_, lean_object* v_hi_3521_, lean_object* v_hhi_3522_, lean_object* v_pivot_3523_, lean_object* v_as_3524_, lean_object* v_i_3525_, lean_object* v_k_3526_, lean_object* v_ilo_3527_, lean_object* v_ik_3528_, lean_object* v_w_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(v_n_3519_, v_lo_3520_, v_hi_3521_, v_hhi_3522_, v_pivot_3523_, v_as_3524_, v_i_3525_, v_k_3526_, v_ilo_3527_, v_ik_3528_, v_w_3529_);
lean_dec_ref(v_pivot_3523_);
lean_dec(v_hi_3521_);
lean_dec(v_lo_3520_);
lean_dec(v_n_3519_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3531_, lean_object* v_k_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v_m_3537_; lean_object* v_a_3538_; uint8_t v___x_3539_; 
v___x_3535_ = lean_nat_add(v_x_3533_, v_x_3534_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v_m_3537_ = lean_nat_shiftr(v___x_3535_, v___x_3536_);
lean_dec(v___x_3535_);
v_a_3538_ = lean_array_fget_borrowed(v_as_3531_, v_m_3537_);
v___x_3539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3538_, v_k_3532_);
if (v___x_3539_ == 0)
{
uint8_t v___x_3540_; 
lean_dec(v_x_3534_);
v___x_3540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3532_, v_a_3538_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec(v_m_3537_);
lean_dec(v_x_3533_);
lean_inc(v_a_3538_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_a_3538_);
return v___x_3541_;
}
else
{
lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = lean_nat_dec_eq(v_m_3537_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = lean_nat_sub(v_m_3537_, v___x_3536_);
lean_dec(v_m_3537_);
v___x_3545_ = lean_nat_dec_lt(v___x_3544_, v_x_3533_);
if (v___x_3545_ == 0)
{
v_x_3534_ = v___x_3544_;
goto _start;
}
else
{
lean_object* v___x_3547_; 
lean_dec(v___x_3544_);
lean_dec(v_x_3533_);
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
}
else
{
lean_object* v___x_3548_; 
lean_dec(v_m_3537_);
lean_dec(v_x_3533_);
v___x_3548_ = lean_box(0);
return v___x_3548_;
}
}
}
else
{
lean_object* v___x_3549_; uint8_t v___x_3550_; 
lean_dec(v_x_3533_);
v___x_3549_ = lean_nat_add(v_m_3537_, v___x_3536_);
lean_dec(v_m_3537_);
v___x_3550_ = lean_nat_dec_le(v___x_3549_, v_x_3534_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec(v___x_3549_);
lean_dec(v_x_3534_);
v___x_3551_ = lean_box(0);
return v___x_3551_;
}
else
{
v_x_3533_ = v___x_3549_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3553_, lean_object* v_k_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3553_, v_k_3554_, v_x_3555_, v_x_3556_);
lean_dec_ref(v_k_3554_);
lean_dec_ref(v_as_3553_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3558_, lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_){
_start:
{
lean_object* v_a_3564_; uint8_t v___x_3568_; 
v___x_3568_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3568_ == 0)
{
lean_dec(v_tactic_3558_);
return v_b_3562_;
}
else
{
lean_object* v___x_3569_; lean_object* v_a_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3569_ = lean_unsigned_to_nat(0u);
v_a_3570_ = lean_array_uget_borrowed(v_as_3559_, v_i_3561_);
v___x_3571_ = lean_array_get_size(v_a_3570_);
v___x_3572_ = lean_nat_dec_lt(v___x_3569_, v___x_3571_);
if (v___x_3572_ == 0)
{
v_a_3564_ = v_b_3562_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_nat_sub(v___x_3571_, v___x_3573_);
v___x_3575_ = lean_nat_dec_le(v___x_3569_, v___x_3574_);
if (v___x_3575_ == 0)
{
lean_dec(v___x_3574_);
v_a_3564_ = v_b_3562_;
goto v___jp_3563_;
}
else
{
lean_object* v_extensions_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_extensions_3576_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3558_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_tactic_3558_);
lean_ctor_set(v___x_3577_, 1, v_extensions_3576_);
v___x_3578_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3570_, v___x_3577_, v___x_3569_, v___x_3574_);
lean_dec_ref_known(v___x_3577_, 2);
if (lean_obj_tag(v___x_3578_) == 1)
{
lean_object* v_val_3579_; lean_object* v_snd_3580_; lean_object* v___x_3581_; 
v_val_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_val_3579_);
lean_dec_ref_known(v___x_3578_, 1);
v_snd_3580_ = lean_ctor_get(v_val_3579_, 1);
lean_inc(v_snd_3580_);
lean_dec(v_val_3579_);
v___x_3581_ = l_Array_append___redArg(v_b_3562_, v_snd_3580_);
lean_dec(v_snd_3580_);
v_a_3564_ = v___x_3581_;
goto v___jp_3563_;
}
else
{
lean_dec(v___x_3578_);
v_a_3564_ = v_b_3562_;
goto v___jp_3563_;
}
}
}
}
v___jp_3563_:
{
size_t v___x_3565_; size_t v___x_3566_; 
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_add(v_i_3561_, v___x_3565_);
v_i_3561_ = v___x_3566_;
v_b_3562_ = v_a_3564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3582_, lean_object* v_as_3583_, lean_object* v_sz_3584_, lean_object* v_i_3585_, lean_object* v_b_3586_){
_start:
{
size_t v_sz_boxed_3587_; size_t v_i_boxed_3588_; lean_object* v_res_3589_; 
v_sz_boxed_3587_ = lean_unbox_usize(v_sz_3584_);
lean_dec(v_sz_3584_);
v_i_boxed_3588_ = lean_unbox_usize(v_i_3585_);
lean_dec(v_i_3585_);
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3582_, v_as_3583_, v_sz_boxed_3587_, v_i_boxed_3588_, v_b_3586_);
lean_dec_ref(v_as_3583_);
return v_res_3589_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_box(1);
v___x_3591_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3592_, lean_object* v_tactic_3593_){
_start:
{
lean_object* v___x_3594_; lean_object* v_toEnvExtension_3595_; lean_object* v_asyncMode_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_importedEntries_3601_; lean_object* v_extensions_3602_; size_t v_sz_3603_; size_t v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3594_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3595_ = lean_ctor_get(v___x_3594_, 0);
v_asyncMode_3596_ = lean_ctor_get(v_toEnvExtension_3595_, 2);
v___x_3597_ = lean_box(1);
v___x_3598_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0, &l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0);
v___x_3599_ = lean_box(0);
lean_inc_ref(v_env_3592_);
v___x_3600_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3598_, v_toEnvExtension_3595_, v_env_3592_, v_asyncMode_3596_, v___x_3599_);
v_importedEntries_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc_ref(v_importedEntries_3601_);
lean_dec(v___x_3600_);
v_extensions_3602_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3603_ = lean_array_size(v_importedEntries_3601_);
v___x_3604_ = ((size_t)0ULL);
lean_inc(v_tactic_3593_);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3593_, v_importedEntries_3601_, v_sz_3603_, v___x_3604_, v_extensions_3602_);
lean_dec_ref(v_importedEntries_3601_);
v___x_3606_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3597_, v___x_3594_, v_env_3592_, v_asyncMode_3596_, v___x_3599_);
v___x_3607_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3606_, v_tactic_3593_);
lean_dec(v_tactic_3593_);
lean_dec(v___x_3606_);
if (lean_obj_tag(v___x_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v___x_3609_; 
v_val_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = l_Array_append___redArg(v___x_3605_, v_val_3608_);
lean_dec(v_val_3608_);
return v___x_3609_;
}
else
{
lean_dec(v___x_3607_);
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3610_, lean_object* v_k_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3610_, v_k_3611_, v_x_3612_, v_x_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3616_, lean_object* v_k_3617_, lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3616_, v_k_3617_, v_x_3618_, v_x_3619_, v_x_3620_);
lean_dec_ref(v_k_3617_);
lean_dec_ref(v_as_3616_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3622_, lean_object* v_pos_3623_){
_start:
{
lean_object* v_str_3624_; lean_object* v_startInclusive_3625_; lean_object* v_endExclusive_3626_; lean_object* v___x_3627_; uint8_t v___y_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v_str_3624_ = lean_ctor_get(v_s_3622_, 0);
v_startInclusive_3625_ = lean_ctor_get(v_s_3622_, 1);
v_endExclusive_3626_ = lean_ctor_get(v_s_3622_, 2);
v___x_3627_ = lean_nat_add(v_startInclusive_3625_, v_pos_3623_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_nat_sub(v_endExclusive_3626_, v___x_3627_);
v___x_3638_ = lean_nat_dec_eq(v___x_3636_, v___x_3637_);
lean_dec(v___x_3637_);
if (v___x_3638_ == 0)
{
uint32_t v___x_3639_; uint8_t v___y_3641_; uint32_t v___x_3646_; uint8_t v___x_3647_; 
v___x_3639_ = lean_string_utf8_get_fast(v_str_3624_, v___x_3627_);
v___x_3646_ = 32;
v___x_3647_ = lean_uint32_dec_eq(v___x_3639_, v___x_3646_);
if (v___x_3647_ == 0)
{
uint32_t v___x_3648_; uint8_t v___x_3649_; 
v___x_3648_ = 9;
v___x_3649_ = lean_uint32_dec_eq(v___x_3639_, v___x_3648_);
v___y_3641_ = v___x_3649_;
goto v___jp_3640_;
}
else
{
v___y_3641_ = v___x_3647_;
goto v___jp_3640_;
}
v___jp_3640_:
{
if (v___y_3641_ == 0)
{
uint32_t v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = 13;
v___x_3643_ = lean_uint32_dec_eq(v___x_3639_, v___x_3642_);
if (v___x_3643_ == 0)
{
uint32_t v___x_3644_; uint8_t v___x_3645_; 
v___x_3644_ = 10;
v___x_3645_ = lean_uint32_dec_eq(v___x_3639_, v___x_3644_);
v___y_3635_ = v___x_3645_;
goto v___jp_3634_;
}
else
{
v___y_3635_ = v___x_3643_;
goto v___jp_3634_;
}
}
else
{
goto v___jp_3628_;
}
}
}
else
{
lean_dec(v___x_3627_);
return v_pos_3623_;
}
v___jp_3628_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3629_ = lean_string_utf8_next_fast(v_str_3624_, v___x_3627_);
v___x_3630_ = lean_nat_sub(v___x_3629_, v___x_3627_);
lean_dec(v___x_3627_);
v___x_3631_ = lean_nat_add(v_pos_3623_, v___x_3630_);
lean_dec(v___x_3630_);
v___x_3632_ = lean_nat_dec_lt(v_pos_3623_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_dec(v___x_3631_);
return v_pos_3623_;
}
else
{
lean_dec(v_pos_3623_);
v_pos_3623_ = v___x_3631_;
goto _start;
}
}
v___jp_3634_:
{
if (v___y_3635_ == 0)
{
lean_dec(v___x_3627_);
return v_pos_3623_;
}
else
{
goto v___jp_3628_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3650_, lean_object* v_pos_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3650_, v_pos_3651_);
lean_dec_ref(v_s_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3655_){
_start:
{
lean_object* v___y_3657_; lean_object* v_str_3660_; lean_object* v_startInclusive_3661_; lean_object* v_endExclusive_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v_str_3660_ = lean_ctor_get(v_str_3655_, 0);
v_startInclusive_3661_ = lean_ctor_get(v_str_3655_, 1);
v_endExclusive_3662_ = lean_ctor_get(v_str_3655_, 2);
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3655_, v___x_3663_);
v___x_3665_ = lean_nat_sub(v_endExclusive_3662_, v_startInclusive_3661_);
v___x_3666_ = lean_nat_dec_eq(v___x_3664_, v___x_3665_);
lean_dec(v___x_3665_);
lean_dec(v___x_3664_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3668_ = lean_string_utf8_extract(v_str_3660_, v_startInclusive_3661_, v_endExclusive_3662_);
v___x_3669_ = lean_string_append(v___x_3667_, v___x_3668_);
lean_dec_ref(v___x_3668_);
v___y_3657_ = v___x_3669_;
goto v___jp_3656_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_string_utf8_extract(v_str_3660_, v_startInclusive_3661_, v_endExclusive_3662_);
v___y_3657_ = v___x_3670_;
goto v___jp_3656_;
}
v___jp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3659_ = lean_string_append(v___y_3657_, v___x_3658_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3671_);
lean_dec_ref(v_str_3671_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0));
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3677_);
lean_dec_ref(v_s_3677_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3679_, lean_object* v___x_3680_, lean_object* v___x_3681_, lean_object* v_a_3682_, lean_object* v_b_3683_){
_start:
{
lean_object* v_it_3685_; lean_object* v_startInclusive_3686_; lean_object* v_endExclusive_3687_; 
if (lean_obj_tag(v_a_3682_) == 0)
{
lean_object* v_currPos_3691_; lean_object* v_searcher_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3718_; 
v_currPos_3691_ = lean_ctor_get(v_a_3682_, 0);
v_searcher_3692_ = lean_ctor_get(v_a_3682_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_a_3682_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3694_ = v_a_3682_;
v_isShared_3695_ = v_isSharedCheck_3718_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_searcher_3692_);
lean_inc(v_currPos_3691_);
lean_dec(v_a_3682_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3718_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_startInclusive_3696_; lean_object* v_endExclusive_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_startInclusive_3696_ = lean_ctor_get(v___x_3680_, 1);
v_endExclusive_3697_ = lean_ctor_get(v___x_3680_, 2);
v___x_3698_ = lean_nat_sub(v_endExclusive_3697_, v_startInclusive_3696_);
v___x_3699_ = lean_nat_dec_eq(v_searcher_3692_, v___x_3698_);
lean_dec(v___x_3698_);
if (v___x_3699_ == 0)
{
uint32_t v___x_3700_; uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3700_ = 10;
v___x_3701_ = lean_string_utf8_get_fast(v_str_3679_, v_searcher_3692_);
v___x_3702_ = lean_uint32_dec_eq(v___x_3701_, v___x_3700_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_string_utf8_next_fast(v_str_3679_, v_searcher_3692_);
lean_dec(v_searcher_3692_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3703_);
v___x_3705_ = v___x_3694_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_currPos_3691_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
v_a_3682_ = v___x_3705_;
goto _start;
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v_slice_3711_; lean_object* v_nextIt_3713_; 
v___x_3708_ = lean_string_utf8_next_fast(v_str_3679_, v_searcher_3692_);
v___x_3709_ = lean_nat_sub(v___x_3708_, v_searcher_3692_);
v___x_3710_ = lean_nat_add(v_searcher_3692_, v___x_3709_);
lean_dec(v___x_3709_);
v_slice_3711_ = l_String_Slice_subslice_x21(v___x_3680_, v_currPos_3691_, v_searcher_3692_);
lean_inc(v___x_3710_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3710_);
lean_ctor_set(v___x_3694_, 0, v___x_3710_);
v_nextIt_3713_ = v___x_3694_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v___x_3710_);
v_nextIt_3713_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v_startInclusive_3714_; lean_object* v_endExclusive_3715_; 
v_startInclusive_3714_ = lean_ctor_get(v_slice_3711_, 0);
lean_inc(v_startInclusive_3714_);
v_endExclusive_3715_ = lean_ctor_get(v_slice_3711_, 1);
lean_inc(v_endExclusive_3715_);
lean_dec_ref(v_slice_3711_);
v_it_3685_ = v_nextIt_3713_;
v_startInclusive_3686_ = v_startInclusive_3714_;
v_endExclusive_3687_ = v_endExclusive_3715_;
goto v___jp_3684_;
}
}
}
else
{
lean_object* v___x_3717_; 
lean_del_object(v___x_3694_);
lean_dec(v_searcher_3692_);
v___x_3717_ = lean_box(1);
lean_inc(v___x_3681_);
v_it_3685_ = v___x_3717_;
v_startInclusive_3686_ = v_currPos_3691_;
v_endExclusive_3687_ = v___x_3681_;
goto v___jp_3684_;
}
}
}
else
{
lean_dec(v___x_3681_);
lean_dec_ref(v_str_3679_);
return v_b_3683_;
}
v___jp_3684_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_inc_ref(v_str_3679_);
v___x_3688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3688_, 0, v_str_3679_);
lean_ctor_set(v___x_3688_, 1, v_startInclusive_3686_);
lean_ctor_set(v___x_3688_, 2, v_endExclusive_3687_);
v___x_3689_ = lean_array_push(v_b_3683_, v___x_3688_);
v_a_3682_ = v_it_3685_;
v_b_3683_ = v___x_3689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3719_, lean_object* v___x_3720_, lean_object* v___x_3721_, lean_object* v_a_3722_, lean_object* v_b_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3719_, v___x_3720_, v___x_3721_, v_a_3722_, v_b_3723_);
lean_dec_ref(v___x_3720_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
if (lean_obj_tag(v_x_3726_) == 0)
{
return v_x_3725_;
}
else
{
lean_object* v_head_3727_; lean_object* v_tail_3728_; lean_object* v___x_3729_; 
v_head_3727_ = lean_ctor_get(v_x_3726_, 0);
v_tail_3728_ = lean_ctor_get(v_x_3726_, 1);
v___x_3729_ = lean_string_append(v_x_3725_, v_head_3727_);
v_x_3725_ = v___x_3729_;
v_x_3726_ = v_tail_3728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3731_, v_x_3732_);
lean_dec(v_x_3732_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
if (lean_obj_tag(v_a_3734_) == 0)
{
lean_object* v___x_3736_; 
v___x_3736_ = l_List_reverse___redArg(v_a_3735_);
return v___x_3736_;
}
else
{
lean_object* v_head_3737_; lean_object* v_tail_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3747_; 
v_head_3737_ = lean_ctor_get(v_a_3734_, 0);
v_tail_3738_ = lean_ctor_get(v_a_3734_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3740_ = v_a_3734_;
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_tail_3738_);
lean_inc(v_head_3737_);
lean_dec(v_a_3734_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3742_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3737_);
lean_dec(v_head_3737_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 1, v_a_3735_);
lean_ctor_set(v___x_3740_, 0, v___x_3742_);
v___x_3744_ = v___x_3740_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_a_3735_);
v___x_3744_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
v_a_3734_ = v_tail_3738_;
v_a_3735_ = v___x_3744_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3752_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v_lines_3759_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = lean_string_utf8_byte_size(v_str_3752_);
lean_inc_ref(v_str_3752_);
v___x_3755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3755_, 0, v_str_3752_);
lean_ctor_set(v___x_3755_, 1, v___x_3753_);
lean_ctor_set(v___x_3755_, 2, v___x_3754_);
v___x_3756_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v___x_3755_);
v___x_3757_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3758_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3752_, v___x_3755_, v___x_3754_, v___x_3756_, v___x_3757_);
lean_dec_ref_known(v___x_3755_, 3);
v_lines_3759_ = lean_array_to_list(v___x_3758_);
if (lean_obj_tag(v_lines_3759_) == 0)
{
lean_object* v___x_3760_; 
v___x_3760_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3760_;
}
else
{
lean_object* v_tail_3761_; 
v_tail_3761_ = lean_ctor_get(v_lines_3759_, 1);
lean_inc(v_tail_3761_);
if (lean_obj_tag(v_tail_3761_) == 0)
{
lean_object* v_head_3762_; lean_object* v_str_3763_; lean_object* v_startInclusive_3764_; lean_object* v_endExclusive_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_head_3762_ = lean_ctor_get(v_lines_3759_, 0);
lean_inc(v_head_3762_);
lean_dec_ref_known(v_lines_3759_, 2);
v_str_3763_ = lean_ctor_get(v_head_3762_, 0);
lean_inc_ref(v_str_3763_);
v_startInclusive_3764_ = lean_ctor_get(v_head_3762_, 1);
lean_inc(v_startInclusive_3764_);
v_endExclusive_3765_ = lean_ctor_get(v_head_3762_, 2);
lean_inc(v_endExclusive_3765_);
lean_dec(v_head_3762_);
v___x_3766_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3767_ = lean_string_utf8_extract(v_str_3763_, v_startInclusive_3764_, v_endExclusive_3765_);
lean_dec(v_endExclusive_3765_);
lean_dec(v_startInclusive_3764_);
lean_dec_ref(v_str_3763_);
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
return v___x_3770_;
}
else
{
lean_object* v_head_3771_; lean_object* v_str_3772_; lean_object* v_startInclusive_3773_; lean_object* v_endExclusive_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_head_3771_ = lean_ctor_get(v_lines_3759_, 0);
lean_inc(v_head_3771_);
lean_dec_ref_known(v_lines_3759_, 2);
v_str_3772_ = lean_ctor_get(v_head_3771_, 0);
lean_inc_ref(v_str_3772_);
v_startInclusive_3773_ = lean_ctor_get(v_head_3771_, 1);
lean_inc(v_startInclusive_3773_);
v_endExclusive_3774_ = lean_ctor_get(v_head_3771_, 2);
lean_inc(v_endExclusive_3774_);
lean_dec(v_head_3771_);
v___x_3775_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3776_ = lean_string_utf8_extract(v_str_3772_, v_startInclusive_3773_, v_endExclusive_3774_);
lean_dec(v_endExclusive_3774_);
lean_dec(v_startInclusive_3773_);
lean_dec_ref(v_str_3772_);
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3779_ = lean_string_append(v___x_3777_, v___x_3778_);
v___x_3780_ = lean_box(0);
v___x_3781_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3761_, v___x_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3783_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3782_, v___x_3781_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_string_append(v___x_3779_, v___x_3783_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3786_ = lean_string_append(v___x_3784_, v___x_3785_);
return v___x_3786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_inst_3790_, lean_object* v_R_3791_, lean_object* v_a_3792_, lean_object* v_b_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3787_, v___x_3788_, v___x_3789_, v_a_3792_, v_b_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3795_, lean_object* v___x_3796_, lean_object* v___x_3797_, lean_object* v_inst_3798_, lean_object* v_R_3799_, lean_object* v_a_3800_, lean_object* v_b_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3795_, v___x_3796_, v___x_3797_, v_inst_3798_, v_R_3799_, v_a_3800_, v_b_3801_);
lean_dec_ref(v___x_3796_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
if (lean_obj_tag(v_a_3803_) == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = l_List_reverse___redArg(v_a_3804_);
return v___x_3805_;
}
else
{
lean_object* v_head_3806_; lean_object* v_tail_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3816_; 
v_head_3806_ = lean_ctor_get(v_a_3803_, 0);
v_tail_3807_ = lean_ctor_get(v_a_3803_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3803_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3809_ = v_a_3803_;
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_tail_3807_);
lean_inc(v_head_3806_);
lean_dec(v_a_3803_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3806_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 1, v_a_3804_);
lean_ctor_set(v___x_3809_, 0, v___x_3811_);
v___x_3813_ = v___x_3809_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_a_3804_);
v___x_3813_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
v_a_3803_ = v_tail_3807_;
v_a_3804_ = v___x_3813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3817_, lean_object* v_pos_3818_){
_start:
{
lean_object* v_str_3819_; lean_object* v_startInclusive_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_str_3819_ = lean_ctor_get(v_s_3817_, 0);
v_startInclusive_3820_ = lean_ctor_get(v_s_3817_, 1);
v___x_3821_ = lean_nat_add(v_startInclusive_3820_, v_pos_3818_);
v___x_3822_ = lean_nat_sub(v___x_3821_, v_startInclusive_3820_);
v___x_3823_ = lean_unsigned_to_nat(0u);
v___x_3824_ = lean_nat_dec_eq(v___x_3822_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___y_3833_; lean_object* v___x_3834_; uint32_t v___x_3835_; uint8_t v___y_3837_; uint32_t v___x_3842_; uint8_t v___x_3843_; 
lean_inc(v_startInclusive_3820_);
lean_inc_ref(v_str_3819_);
v___x_3825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3825_, 0, v_str_3819_);
lean_ctor_set(v___x_3825_, 1, v_startInclusive_3820_);
lean_ctor_set(v___x_3825_, 2, v___x_3821_);
v___x_3826_ = lean_unsigned_to_nat(1u);
v___x_3827_ = lean_nat_sub(v___x_3822_, v___x_3826_);
lean_dec(v___x_3822_);
v___x_3828_ = l_String_Slice_posLE(v___x_3825_, v___x_3827_);
lean_dec_ref_known(v___x_3825_, 3);
v___x_3834_ = lean_nat_add(v_startInclusive_3820_, v___x_3828_);
v___x_3835_ = lean_string_utf8_get_fast(v_str_3819_, v___x_3834_);
lean_dec(v___x_3834_);
v___x_3842_ = 32;
v___x_3843_ = lean_uint32_dec_eq(v___x_3835_, v___x_3842_);
if (v___x_3843_ == 0)
{
uint32_t v___x_3844_; uint8_t v___x_3845_; 
v___x_3844_ = 9;
v___x_3845_ = lean_uint32_dec_eq(v___x_3835_, v___x_3844_);
v___y_3837_ = v___x_3845_;
goto v___jp_3836_;
}
else
{
v___y_3837_ = v___x_3843_;
goto v___jp_3836_;
}
v___jp_3829_:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_nat_dec_lt(v___x_3828_, v_pos_3818_);
if (v___x_3830_ == 0)
{
lean_dec(v___x_3828_);
return v_pos_3818_;
}
else
{
lean_dec(v_pos_3818_);
v_pos_3818_ = v___x_3828_;
goto _start;
}
}
v___jp_3832_:
{
if (v___y_3833_ == 0)
{
lean_dec(v___x_3828_);
return v_pos_3818_;
}
else
{
goto v___jp_3829_;
}
}
v___jp_3836_:
{
if (v___y_3837_ == 0)
{
uint32_t v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = 13;
v___x_3839_ = lean_uint32_dec_eq(v___x_3835_, v___x_3838_);
if (v___x_3839_ == 0)
{
uint32_t v___x_3840_; uint8_t v___x_3841_; 
v___x_3840_ = 10;
v___x_3841_ = lean_uint32_dec_eq(v___x_3835_, v___x_3840_);
v___y_3833_ = v___x_3841_;
goto v___jp_3832_;
}
else
{
v___y_3833_ = v___x_3839_;
goto v___jp_3832_;
}
}
else
{
goto v___jp_3829_;
}
}
}
else
{
lean_dec(v___x_3822_);
lean_dec(v___x_3821_);
return v_pos_3818_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3846_, lean_object* v_pos_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3846_, v_pos_3847_);
lean_dec_ref(v_s_3846_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3850_, lean_object* v_tactic_3851_){
_start:
{
lean_object* v_exts_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_exts_3852_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3850_, v_tactic_3851_);
v___x_3853_ = lean_array_get_size(v_exts_3852_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_nat_dec_eq(v___x_3853_, v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3856_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3857_ = lean_array_to_list(v_exts_3852_);
v___x_3858_ = lean_box(0);
v___x_3859_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3857_, v___x_3858_);
v___x_3860_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3861_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3860_, v___x_3859_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_string_append(v___x_3856_, v___x_3861_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = lean_string_utf8_byte_size(v___x_3862_);
lean_inc_ref(v___x_3862_);
v___x_3864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v___x_3854_);
lean_ctor_set(v___x_3864_, 2, v___x_3863_);
v___x_3865_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3864_, v___x_3863_);
lean_dec_ref_known(v___x_3864_, 3);
v___x_3866_ = lean_string_utf8_extract(v___x_3862_, v___x_3854_, v___x_3865_);
lean_dec(v___x_3865_);
lean_dec_ref(v___x_3862_);
return v___x_3866_;
}
else
{
lean_object* v___x_3867_; 
lean_dec_ref(v_exts_3852_);
v___x_3867_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3868_, lean_object* v_x_3869_){
_start:
{
lean_object* v_fst_3870_; lean_object* v_snd_3871_; lean_object* v___x_3872_; 
v_fst_3870_ = lean_ctor_get(v_x_3869_, 0);
lean_inc(v_fst_3870_);
v_snd_3871_ = lean_ctor_get(v_x_3869_, 1);
lean_inc(v_snd_3871_);
lean_dec_ref(v_x_3869_);
v___x_3872_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3870_, v_snd_3871_, v_as_3868_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3873_, lean_object* v_x_3874_){
_start:
{
if (lean_obj_tag(v_x_3874_) == 0)
{
lean_object* v_k_3875_; lean_object* v_v_3876_; lean_object* v_l_3877_; lean_object* v_r_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_k_3875_ = lean_ctor_get(v_x_3874_, 1);
v_v_3876_ = lean_ctor_get(v_x_3874_, 2);
v_l_3877_ = lean_ctor_get(v_x_3874_, 3);
v_r_3878_ = lean_ctor_get(v_x_3874_, 4);
v___x_3879_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3873_, v_l_3877_);
lean_inc(v_v_3876_);
lean_inc(v_k_3875_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_k_3875_);
lean_ctor_set(v___x_3880_, 1, v_v_3876_);
v___x_3881_ = lean_array_push(v___x_3879_, v___x_3880_);
v_init_3873_ = v___x_3881_;
v_x_3874_ = v_r_3878_;
goto _start;
}
else
{
return v_init_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3883_, lean_object* v_x_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3883_, v_x_3884_);
lean_dec(v_x_3884_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3886_, lean_object* v_pivot_3887_, lean_object* v_as_3888_, lean_object* v_i_3889_, lean_object* v_k_3890_){
_start:
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_nat_dec_lt(v_k_3890_, v_hi_3886_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec(v_k_3890_);
v___x_3892_ = lean_array_fswap(v_as_3888_, v_i_3889_, v_hi_3886_);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_i_3889_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v_fst_3895_; lean_object* v_fst_3896_; uint8_t v___x_3897_; 
v___x_3894_ = lean_array_fget_borrowed(v_as_3888_, v_k_3890_);
v_fst_3895_ = lean_ctor_get(v___x_3894_, 0);
v_fst_3896_ = lean_ctor_get(v_pivot_3887_, 0);
v___x_3897_ = l_Lean_Name_quickLt(v_fst_3895_, v_fst_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_k_3890_, v___x_3898_);
lean_dec(v_k_3890_);
v_k_3890_ = v___x_3899_;
goto _start;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3901_ = lean_array_fswap(v_as_3888_, v_i_3889_, v_k_3890_);
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_add(v_i_3889_, v___x_3902_);
lean_dec(v_i_3889_);
v___x_3904_ = lean_nat_add(v_k_3890_, v___x_3902_);
lean_dec(v_k_3890_);
v_as_3888_ = v___x_3901_;
v_i_3889_ = v___x_3903_;
v_k_3890_ = v___x_3904_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3906_, lean_object* v_pivot_3907_, lean_object* v_as_3908_, lean_object* v_i_3909_, lean_object* v_k_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3906_, v_pivot_3907_, v_as_3908_, v_i_3909_, v_k_3910_);
lean_dec_ref(v_pivot_3907_);
lean_dec(v_hi_3906_);
return v_res_3911_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3912_, lean_object* v_x2_3913_){
_start:
{
lean_object* v_fst_3914_; lean_object* v_fst_3915_; uint8_t v___x_3916_; 
v_fst_3914_ = lean_ctor_get(v_x1_3912_, 0);
v_fst_3915_ = lean_ctor_get(v_x2_3913_, 0);
v___x_3916_ = l_Lean_Name_quickLt(v_fst_3914_, v_fst_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3917_, lean_object* v_x2_3918_){
_start:
{
uint8_t v_res_3919_; lean_object* v_r_3920_; 
v_res_3919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3917_, v_x2_3918_);
lean_dec_ref(v_x2_3918_);
lean_dec_ref(v_x1_3917_);
v_r_3920_ = lean_box(v_res_3919_);
return v_r_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3921_, lean_object* v_as_3922_, lean_object* v_lo_3923_, lean_object* v_hi_3924_){
_start:
{
lean_object* v___y_3926_; uint8_t v___x_3936_; 
v___x_3936_ = lean_nat_dec_lt(v_lo_3923_, v_hi_3924_);
if (v___x_3936_ == 0)
{
lean_dec(v_lo_3923_);
return v_as_3922_;
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v_mid_3939_; lean_object* v___y_3941_; lean_object* v___y_3947_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3937_ = lean_nat_add(v_lo_3923_, v_hi_3924_);
v___x_3938_ = lean_unsigned_to_nat(1u);
v_mid_3939_ = lean_nat_shiftr(v___x_3937_, v___x_3938_);
lean_dec(v___x_3937_);
v___x_3952_ = lean_array_fget_borrowed(v_as_3922_, v_mid_3939_);
v___x_3953_ = lean_array_fget_borrowed(v_as_3922_, v_lo_3923_);
v___x_3954_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3952_, v___x_3953_);
if (v___x_3954_ == 0)
{
v___y_3947_ = v_as_3922_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_array_fswap(v_as_3922_, v_lo_3923_, v_mid_3939_);
v___y_3947_ = v___x_3955_;
goto v___jp_3946_;
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3942_ = lean_array_fget_borrowed(v___y_3941_, v_mid_3939_);
v___x_3943_ = lean_array_fget_borrowed(v___y_3941_, v_hi_3924_);
v___x_3944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3942_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_dec(v_mid_3939_);
v___y_3926_ = v___y_3941_;
goto v___jp_3925_;
}
else
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_array_fswap(v___y_3941_, v_mid_3939_, v_hi_3924_);
lean_dec(v_mid_3939_);
v___y_3926_ = v___x_3945_;
goto v___jp_3925_;
}
}
v___jp_3946_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = lean_array_fget_borrowed(v___y_3947_, v_hi_3924_);
v___x_3949_ = lean_array_fget_borrowed(v___y_3947_, v_lo_3923_);
v___x_3950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
v___y_3941_ = v___y_3947_;
goto v___jp_3940_;
}
else
{
lean_object* v___x_3951_; 
v___x_3951_ = lean_array_fswap(v___y_3947_, v_lo_3923_, v_hi_3924_);
v___y_3941_ = v___x_3951_;
goto v___jp_3940_;
}
}
}
v___jp_3925_:
{
lean_object* v_pivot_3927_; lean_object* v___x_3928_; lean_object* v_fst_3929_; lean_object* v_snd_3930_; uint8_t v___x_3931_; 
v_pivot_3927_ = lean_array_fget(v___y_3926_, v_hi_3924_);
lean_inc_n(v_lo_3923_, 2);
v___x_3928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3924_, v_pivot_3927_, v___y_3926_, v_lo_3923_, v_lo_3923_);
lean_dec(v_pivot_3927_);
v_fst_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_fst_3929_);
v_snd_3930_ = lean_ctor_get(v___x_3928_, 1);
lean_inc(v_snd_3930_);
lean_dec_ref(v___x_3928_);
v___x_3931_ = lean_nat_dec_le(v_hi_3924_, v_fst_3929_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3921_, v_snd_3930_, v_lo_3923_, v_fst_3929_);
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_nat_add(v_fst_3929_, v___x_3933_);
lean_dec(v_fst_3929_);
v_as_3922_ = v___x_3932_;
v_lo_3923_ = v___x_3934_;
goto _start;
}
else
{
lean_dec(v_fst_3929_);
lean_dec(v_lo_3923_);
return v_snd_3930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3956_, lean_object* v_as_3957_, lean_object* v_lo_3958_, lean_object* v_hi_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3956_, v_as_3957_, v_lo_3958_, v_hi_3959_);
lean_dec(v_hi_3959_);
lean_dec(v_n_3956_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3963_, lean_object* v_s_3964_){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___y_3970_; lean_object* v___y_3971_; uint8_t v___x_3974_; 
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3967_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3966_, v_s_3964_);
v___x_3968_ = lean_array_get_size(v___x_3967_);
v___x_3974_ = lean_nat_dec_eq(v___x_3968_, v___x_3965_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___y_3978_; uint8_t v___x_3980_; 
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_nat_sub(v___x_3968_, v___x_3975_);
v___x_3980_ = lean_nat_dec_le(v___x_3965_, v___x_3976_);
if (v___x_3980_ == 0)
{
lean_inc(v___x_3976_);
v___y_3978_ = v___x_3976_;
goto v___jp_3977_;
}
else
{
v___y_3978_ = v___x_3965_;
goto v___jp_3977_;
}
v___jp_3977_:
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_nat_dec_le(v___y_3978_, v___x_3976_);
if (v___x_3979_ == 0)
{
lean_dec(v___x_3976_);
lean_inc(v___y_3978_);
v___y_3970_ = v___y_3978_;
v___y_3971_ = v___y_3978_;
goto v___jp_3969_;
}
else
{
v___y_3970_ = v___y_3978_;
v___y_3971_ = v___x_3976_;
goto v___jp_3969_;
}
}
}
else
{
lean_object* v___x_3981_; 
lean_inc_ref_n(v___x_3967_, 2);
v___x_3981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3967_);
lean_ctor_set(v___x_3981_, 1, v___x_3967_);
lean_ctor_set(v___x_3981_, 2, v___x_3967_);
return v___x_3981_;
}
v___jp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3968_, v___x_3967_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_inc_ref_n(v___x_3972_, 2);
v___x_3973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
lean_ctor_set(v___x_3973_, 2, v___x_3972_);
return v___x_3973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3982_, lean_object* v_s_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3982_, v_s_3983_);
lean_dec(v_s_3983_);
lean_dec_ref(v_x_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3988_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3987_, v_es_3985_);
v___x_3989_ = lean_array_get_size(v___x_3988_);
v___x_3990_ = lean_nat_dec_eq(v___x_3989_, v___x_3986_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___y_3994_; uint8_t v___x_3998_; 
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_nat_sub(v___x_3989_, v___x_3991_);
v___x_3998_ = lean_nat_dec_le(v___x_3986_, v___x_3992_);
if (v___x_3998_ == 0)
{
lean_inc(v___x_3992_);
v___y_3994_ = v___x_3992_;
goto v___jp_3993_;
}
else
{
v___y_3994_ = v___x_3986_;
goto v___jp_3993_;
}
v___jp_3993_:
{
uint8_t v___x_3995_; 
v___x_3995_ = lean_nat_dec_le(v___y_3994_, v___x_3992_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
lean_dec(v___x_3992_);
lean_inc(v___y_3994_);
v___x_3996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3989_, v___x_3988_, v___y_3994_, v___y_3994_);
lean_dec(v___y_3994_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3989_, v___x_3988_, v___y_3994_, v___x_3992_);
lean_dec(v___x_3992_);
return v___x_3997_;
}
}
}
else
{
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_3999_);
lean_dec(v_es_3999_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_4001_, lean_object* v_x_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4001_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_4006_, lean_object* v_x_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_4006_, v_x_4007_, v___y_4008_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v_x_4007_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_4037_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_4040_, lean_object* v_t_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_4040_, v_t_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4043_, lean_object* v_t_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_4043_, v_t_4044_);
lean_dec(v_t_4044_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_4046_, lean_object* v_as_4047_, lean_object* v_lo_4048_, lean_object* v_hi_4049_, lean_object* v_w_4050_, lean_object* v_hlo_4051_, lean_object* v_hhi_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_4046_, v_as_4047_, v_lo_4048_, v_hi_4049_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_4054_, lean_object* v_as_4055_, lean_object* v_lo_4056_, lean_object* v_hi_4057_, lean_object* v_w_4058_, lean_object* v_hlo_4059_, lean_object* v_hhi_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_4054_, v_as_4055_, v_lo_4056_, v_hi_4057_, v_w_4058_, v_hlo_4059_, v_hhi_4060_);
lean_dec(v_hi_4057_);
lean_dec(v_n_4054_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_4062_, lean_object* v_lo_4063_, lean_object* v_hi_4064_, lean_object* v_hhi_4065_, lean_object* v_pivot_4066_, lean_object* v_as_4067_, lean_object* v_i_4068_, lean_object* v_k_4069_, lean_object* v_ilo_4070_, lean_object* v_ik_4071_, lean_object* v_w_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_4064_, v_pivot_4066_, v_as_4067_, v_i_4068_, v_k_4069_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_4074_, lean_object* v_lo_4075_, lean_object* v_hi_4076_, lean_object* v_hhi_4077_, lean_object* v_pivot_4078_, lean_object* v_as_4079_, lean_object* v_i_4080_, lean_object* v_k_4081_, lean_object* v_ilo_4082_, lean_object* v_ik_4083_, lean_object* v_w_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(v_n_4074_, v_lo_4075_, v_hi_4076_, v_hhi_4077_, v_pivot_4078_, v_as_4079_, v_i_4080_, v_k_4081_, v_ilo_4082_, v_ik_4083_, v_w_4084_);
lean_dec_ref(v_pivot_4078_);
lean_dec(v_hi_4076_);
lean_dec(v_lo_4075_);
lean_dec(v_n_4074_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_4087_, lean_object* v___x_4088_, lean_object* v_toPure_4089_, lean_object* v___f_4090_, lean_object* v_env_4091_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4091_, v_tac_4087_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v___x_4096_; lean_object* v_toEnvExtension_4097_; lean_object* v_asyncMode_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec_ref(v___f_4090_);
v___x_4096_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4097_ = lean_ctor_get(v___x_4096_, 0);
v_asyncMode_4098_ = lean_ctor_get(v_toEnvExtension_4097_, 2);
v___x_4099_ = lean_box(0);
v___x_4100_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4088_, v___x_4096_, v_env_4091_, v_asyncMode_4098_, v___x_4099_);
v___x_4101_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4100_, v_tac_4087_);
lean_dec(v_tac_4087_);
lean_dec(v___x_4100_);
v___x_4102_ = lean_apply_2(v_toPure_4089_, lean_box(0), v___x_4101_);
return v___x_4102_;
}
else
{
lean_object* v_val_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v_val_4103_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4104_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4105_ = 0;
v___x_4106_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4088_, v___x_4104_, v_env_4091_, v_val_4103_, v___x_4105_);
lean_dec(v_val_4103_);
lean_dec_ref(v_env_4091_);
v___x_4107_ = lean_unsigned_to_nat(0u);
v___x_4108_ = lean_array_get_size(v___x_4106_);
v___x_4109_ = lean_nat_dec_lt(v___x_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_dec_ref(v___x_4106_);
lean_dec_ref(v___f_4090_);
lean_dec(v_tac_4087_);
goto v___jp_4092_;
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4110_ = lean_unsigned_to_nat(1u);
v___x_4111_ = lean_nat_sub(v___x_4108_, v___x_4110_);
v___x_4112_ = lean_nat_dec_le(v___x_4107_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_dec(v___x_4111_);
lean_dec_ref(v___x_4106_);
lean_dec_ref(v___f_4090_);
lean_dec(v_tac_4087_);
goto v___jp_4092_;
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4113_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_tac_4087_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_4116_ = l_Array_binSearchAux___redArg(v___f_4090_, v___x_4115_, v___x_4106_, v___x_4114_, v___x_4107_, v___x_4111_);
lean_dec_ref(v___x_4106_);
if (lean_obj_tag(v___x_4116_) == 0)
{
goto v___jp_4092_;
}
else
{
lean_object* v_val_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
v_val_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_val_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v_snd_4121_; lean_object* v___x_4123_; 
v_snd_4121_ = lean_ctor_get(v_val_4117_, 1);
lean_inc(v_snd_4121_);
lean_dec(v_val_4117_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v_snd_4121_);
v___x_4123_ = v___x_4119_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_snd_4121_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_apply_2(v_toPure_4089_, lean_box(0), v___x_4123_);
return v___x_4124_;
}
}
}
}
}
}
v___jp_4092_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_apply_2(v_toPure_4089_, lean_box(0), v___x_4093_);
return v___x_4094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_4128_, lean_object* v_inst_4129_, lean_object* v_tac_4130_){
_start:
{
lean_object* v_toApplicative_4131_; lean_object* v_toBind_4132_; lean_object* v_getEnv_4133_; lean_object* v_toPure_4134_; lean_object* v___f_4135_; lean_object* v___x_4136_; lean_object* v___f_4137_; lean_object* v___x_4138_; 
v_toApplicative_4131_ = lean_ctor_get(v_inst_4128_, 0);
lean_inc_ref(v_toApplicative_4131_);
v_toBind_4132_ = lean_ctor_get(v_inst_4128_, 1);
lean_inc(v_toBind_4132_);
lean_dec_ref(v_inst_4128_);
v_getEnv_4133_ = lean_ctor_get(v_inst_4129_, 0);
lean_inc(v_getEnv_4133_);
lean_dec_ref(v_inst_4129_);
v_toPure_4134_ = lean_ctor_get(v_toApplicative_4131_, 1);
lean_inc(v_toPure_4134_);
lean_dec_ref(v_toApplicative_4131_);
v___f_4135_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0));
v___x_4136_ = lean_box(1);
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4137_, 0, v_tac_4130_);
lean_closure_set(v___f_4137_, 1, v___x_4136_);
lean_closure_set(v___f_4137_, 2, v_toPure_4134_);
lean_closure_set(v___f_4137_, 3, v___f_4135_);
v___x_4138_ = lean_apply_4(v_toBind_4132_, lean_box(0), lean_box(0), v_getEnv_4133_, v___f_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_4139_, lean_object* v_inst_4140_, lean_object* v_inst_4141_, lean_object* v_tac_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_4140_, v_inst_4141_, v_tac_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4144_, lean_object* v_k_4145_, lean_object* v_x_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v_m_4150_; lean_object* v_a_4151_; uint8_t v___x_4152_; 
v___x_4148_ = lean_nat_add(v_x_4146_, v_x_4147_);
v___x_4149_ = lean_unsigned_to_nat(1u);
v_m_4150_ = lean_nat_shiftr(v___x_4148_, v___x_4149_);
lean_dec(v___x_4148_);
v_a_4151_ = lean_array_fget_borrowed(v_as_4144_, v_m_4150_);
v___x_4152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_4151_, v_k_4145_);
if (v___x_4152_ == 0)
{
uint8_t v___x_4153_; 
lean_dec(v_x_4147_);
v___x_4153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_4145_, v_a_4151_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec(v_m_4150_);
lean_dec(v_x_4146_);
lean_inc(v_a_4151_);
v___x_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_a_4151_);
return v___x_4154_;
}
else
{
lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = lean_nat_dec_eq(v_m_4150_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; uint8_t v___x_4158_; 
v___x_4157_ = lean_nat_sub(v_m_4150_, v___x_4149_);
lean_dec(v_m_4150_);
v___x_4158_ = lean_nat_dec_lt(v___x_4157_, v_x_4146_);
if (v___x_4158_ == 0)
{
v_x_4147_ = v___x_4157_;
goto _start;
}
else
{
lean_object* v___x_4160_; 
lean_dec(v___x_4157_);
lean_dec(v_x_4146_);
v___x_4160_ = lean_box(0);
return v___x_4160_;
}
}
else
{
lean_object* v___x_4161_; 
lean_dec(v_m_4150_);
lean_dec(v_x_4146_);
v___x_4161_ = lean_box(0);
return v___x_4161_;
}
}
}
else
{
lean_object* v___x_4162_; uint8_t v___x_4163_; 
lean_dec(v_x_4146_);
v___x_4162_ = lean_nat_add(v_m_4150_, v___x_4149_);
lean_dec(v_m_4150_);
v___x_4163_ = lean_nat_dec_le(v___x_4162_, v_x_4147_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_dec(v___x_4162_);
lean_dec(v_x_4147_);
v___x_4164_ = lean_box(0);
return v___x_4164_;
}
else
{
v_x_4146_ = v___x_4162_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4166_, lean_object* v_k_4167_, lean_object* v_x_4168_, lean_object* v_x_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4166_, v_k_4167_, v_x_4168_, v_x_4169_);
lean_dec_ref(v_k_4167_);
lean_dec_ref(v_as_4166_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___x_4174_; lean_object* v_env_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4174_ = lean_st_ref_get(v___y_4172_);
v_env_4178_ = lean_ctor_get(v___x_4174_, 0);
lean_inc_ref(v_env_4178_);
lean_dec(v___x_4174_);
v___x_4179_ = lean_box(1);
v___x_4180_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4178_, v_tac_4171_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v___x_4181_; lean_object* v_toEnvExtension_4182_; lean_object* v_asyncMode_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4181_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4182_ = lean_ctor_get(v___x_4181_, 0);
v_asyncMode_4183_ = lean_ctor_get(v_toEnvExtension_4182_, 2);
v___x_4184_ = lean_box(0);
v___x_4185_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4179_, v___x_4181_, v_env_4178_, v_asyncMode_4183_, v___x_4184_);
v___x_4186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4185_, v_tac_4171_);
lean_dec(v_tac_4171_);
lean_dec(v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
else
{
lean_object* v_val_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4216_; 
v_val_4188_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4190_ = v___x_4180_;
v_isShared_4191_ = v_isSharedCheck_4216_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_val_4188_);
lean_dec(v___x_4180_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4216_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v___x_4192_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4193_ = 0;
v___x_4194_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4179_, v___x_4192_, v_env_4178_, v_val_4188_, v___x_4193_);
lean_dec(v_val_4188_);
lean_dec_ref(v_env_4178_);
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = lean_array_get_size(v___x_4194_);
v___x_4197_ = lean_nat_dec_lt(v___x_4195_, v___x_4196_);
if (v___x_4197_ == 0)
{
lean_dec_ref(v___x_4194_);
lean_del_object(v___x_4190_);
lean_dec(v_tac_4171_);
goto v___jp_4175_;
}
else
{
lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4198_ = lean_unsigned_to_nat(1u);
v___x_4199_ = lean_nat_sub(v___x_4196_, v___x_4198_);
v___x_4200_ = lean_nat_dec_le(v___x_4195_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_dec(v___x_4199_);
lean_dec_ref(v___x_4194_);
lean_del_object(v___x_4190_);
lean_dec(v_tac_4171_);
goto v___jp_4175_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4201_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v_tac_4171_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4194_, v___x_4202_, v___x_4195_, v___x_4199_);
lean_dec_ref_known(v___x_4202_, 2);
lean_dec_ref(v___x_4194_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_del_object(v___x_4190_);
goto v___jp_4175_;
}
else
{
lean_object* v_val_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4215_; 
v_val_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4215_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_val_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4215_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v_snd_4208_; lean_object* v___x_4210_; 
v_snd_4208_ = lean_ctor_get(v_val_4204_, 1);
lean_inc(v_snd_4208_);
lean_dec(v_val_4204_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v_snd_4208_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_snd_4208_);
v___x_4210_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4212_; 
if (v_isShared_4191_ == 0)
{
lean_ctor_set_tag(v___x_4190_, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4210_);
v___x_4212_ = v___x_4190_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
}
}
}
v___jp_4175_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_box(0);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
return v___x_4177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4217_, v___y_4218_);
lean_dec(v___y_4218_);
return v_res_4220_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4223_ = l_Lean_stringToMessageData(v___x_4222_);
return v___x_4223_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4226_ = l_Lean_stringToMessageData(v___x_4225_);
return v___x_4226_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4229_ = l_Lean_stringToMessageData(v___x_4228_);
return v___x_4229_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4232_ = l_Lean_stringToMessageData(v___x_4231_);
return v___x_4232_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4235_ = l_Lean_stringToMessageData(v___x_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_4242_, lean_object* v___x_4243_, lean_object* v___x_4244_, lean_object* v___x_4245_, lean_object* v_name_4246_, lean_object* v_decl_4247_, lean_object* v_stx_4248_, uint8_t v_kind_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; uint8_t v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v_name_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; uint8_t v___x_4408_; uint8_t v___x_4409_; 
v___x_4408_ = 0;
v___x_4409_ = l_Lean_instBEqAttributeKind_beq(v_kind_4249_, v___x_4408_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; 
lean_dec(v_stx_4248_);
lean_dec(v_decl_4247_);
lean_dec_ref(v___x_4245_);
lean_dec_ref(v___x_4244_);
lean_dec_ref(v___x_4243_);
lean_dec(v___x_4242_);
v___x_4410_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_4246_, v_kind_4249_, v___y_4250_, v___y_4251_);
return v___x_4410_;
}
else
{
goto v___jp_4367_;
}
v___jp_4253_:
{
lean_object* v___x_4256_; lean_object* v_env_4257_; lean_object* v_nextMacroScope_4258_; lean_object* v_ngen_4259_; lean_object* v_auxDeclNGen_4260_; lean_object* v_traceState_4261_; lean_object* v_messages_4262_; lean_object* v_infoState_4263_; lean_object* v_snapshotTasks_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4280_; 
v___x_4256_ = lean_st_ref_take(v___y_4255_);
v_env_4257_ = lean_ctor_get(v___x_4256_, 0);
v_nextMacroScope_4258_ = lean_ctor_get(v___x_4256_, 1);
v_ngen_4259_ = lean_ctor_get(v___x_4256_, 2);
v_auxDeclNGen_4260_ = lean_ctor_get(v___x_4256_, 3);
v_traceState_4261_ = lean_ctor_get(v___x_4256_, 4);
v_messages_4262_ = lean_ctor_get(v___x_4256_, 6);
v_infoState_4263_ = lean_ctor_get(v___x_4256_, 7);
v_snapshotTasks_4264_ = lean_ctor_get(v___x_4256_, 8);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4280_ == 0)
{
lean_object* v_unused_4281_; 
v_unused_4281_ = lean_ctor_get(v___x_4256_, 5);
lean_dec(v_unused_4281_);
v___x_4266_ = v___x_4256_;
v_isShared_4267_ = v_isSharedCheck_4280_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_snapshotTasks_4264_);
lean_inc(v_infoState_4263_);
lean_inc(v_messages_4262_);
lean_inc(v_traceState_4261_);
lean_inc(v_auxDeclNGen_4260_);
lean_inc(v_ngen_4259_);
lean_inc(v_nextMacroScope_4258_);
lean_inc(v_env_4257_);
lean_dec(v___x_4256_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4280_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v_toEnvExtension_4269_; lean_object* v_asyncMode_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4268_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4269_ = lean_ctor_get(v___x_4268_, 0);
v_asyncMode_4270_ = lean_ctor_get(v_toEnvExtension_4269_, 2);
v___x_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4271_, 0, v_decl_4247_);
lean_ctor_set(v___x_4271_, 1, v___y_4254_);
v___x_4272_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4268_, v_env_4257_, v___x_4271_, v_asyncMode_4270_, v___x_4242_);
v___x_4273_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 5, v___x_4273_);
lean_ctor_set(v___x_4266_, 0, v___x_4272_);
v___x_4275_ = v___x_4266_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4272_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_nextMacroScope_4258_);
lean_ctor_set(v_reuseFailAlloc_4279_, 2, v_ngen_4259_);
lean_ctor_set(v_reuseFailAlloc_4279_, 3, v_auxDeclNGen_4260_);
lean_ctor_set(v_reuseFailAlloc_4279_, 4, v_traceState_4261_);
lean_ctor_set(v_reuseFailAlloc_4279_, 5, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4279_, 6, v_messages_4262_);
lean_ctor_set(v_reuseFailAlloc_4279_, 7, v_infoState_4263_);
lean_ctor_set(v_reuseFailAlloc_4279_, 8, v_snapshotTasks_4264_);
v___x_4275_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = lean_st_ref_set(v___y_4255_, v___x_4275_);
v___x_4277_ = lean_box(0);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
}
}
v___jp_4282_:
{
lean_object* v___x_4286_; lean_object* v_a_4287_; 
lean_inc(v_decl_4247_);
v___x_4286_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_4247_, v___y_4285_);
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref(v___x_4286_);
if (lean_obj_tag(v_a_4287_) == 1)
{
lean_object* v_val_4288_; lean_object* v___x_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
lean_dec_ref(v___y_4283_);
lean_dec(v___x_4242_);
v_val_4288_ = lean_ctor_get(v_a_4287_, 0);
lean_inc(v_val_4288_);
lean_dec_ref_known(v_a_4287_, 1);
v___x_4289_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4290_ = 0;
v___x_4291_ = l_Lean_MessageData_ofConstName(v_decl_4247_, v___x_4290_);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4289_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = l_Lean_stringToMessageData(v_val_4288_);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4298_, v___y_4284_, v___y_4285_);
return v___x_4299_;
}
else
{
lean_dec(v_a_4287_);
v___y_4254_ = v___y_4283_;
v___y_4255_ = v___y_4285_;
goto v___jp_4253_;
}
}
v___jp_4300_:
{
lean_object* v___x_4304_; lean_object* v_env_4305_; lean_object* v___x_4306_; 
v___x_4304_ = lean_st_ref_get(v___y_4303_);
v_env_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc_ref(v_env_4305_);
lean_dec(v___x_4304_);
lean_inc(v_decl_4247_);
v___x_4306_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4305_, v_decl_4247_);
if (lean_obj_tag(v___x_4306_) == 1)
{
lean_object* v_val_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_dec_ref(v___y_4301_);
lean_dec(v___x_4242_);
v_val_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_val_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4309_ = 0;
v___x_4310_ = l_Lean_MessageData_ofConstName(v_decl_4247_, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4308_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = l_Lean_MessageData_ofConstName(v_val_4307_, v___x_4309_);
v___x_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4313_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v___x_4308_);
v___x_4317_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4248_, v___x_4316_, v___y_4302_, v___y_4303_);
lean_dec(v_stx_4248_);
return v___x_4317_;
}
else
{
lean_dec(v___x_4306_);
lean_dec(v_stx_4248_);
v___y_4283_ = v___y_4301_;
v___y_4284_ = v___y_4302_;
v___y_4285_ = v___y_4303_;
goto v___jp_4282_;
}
}
v___jp_4318_:
{
lean_object* v___x_4323_; lean_object* v_env_4324_; lean_object* v___x_4325_; 
v___x_4323_ = lean_st_ref_get(v___y_4322_);
v_env_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc_ref(v_env_4324_);
lean_dec(v___x_4323_);
v___x_4325_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4324_, v_decl_4247_);
lean_dec_ref(v_env_4324_);
if (lean_obj_tag(v___x_4325_) == 1)
{
lean_object* v_val_4326_; lean_object* v___x_4327_; lean_object* v_env_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
lean_dec_ref(v___y_4320_);
lean_dec(v___x_4242_);
v_val_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_val_4326_);
lean_dec_ref_known(v___x_4325_, 1);
v___x_4327_ = lean_st_ref_get(v___y_4322_);
v_env_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc_ref(v_env_4328_);
lean_dec(v___x_4327_);
v___x_4329_ = l_Lean_Environment_allImportedModuleNames(v_env_4328_);
lean_dec_ref(v_env_4328_);
v___x_4330_ = lean_array_get_size(v___x_4329_);
v___x_4331_ = lean_nat_dec_lt(v_val_4326_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
lean_dec_ref(v___x_4329_);
lean_dec(v_val_4326_);
v___x_4332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4333_ = l_Lean_MessageData_ofConstName(v_decl_4247_, v___y_4319_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4248_, v___x_4336_, v___y_4321_, v___y_4322_);
lean_dec(v_stx_4248_);
return v___x_4337_;
}
else
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4338_ = lean_array_fget(v___x_4329_, v_val_4326_);
lean_dec(v_val_4326_);
lean_dec_ref(v___x_4329_);
v___x_4339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4340_ = l_Lean_MessageData_ofConstName(v_decl_4247_, v___y_4319_);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l_Lean_MessageData_ofName(v___x_4338_);
v___x_4345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4343_);
lean_ctor_set(v___x_4345_, 1, v___x_4344_);
v___x_4346_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4248_, v___x_4347_, v___y_4321_, v___y_4322_);
lean_dec(v_stx_4248_);
return v___x_4348_;
}
}
else
{
lean_dec(v___x_4325_);
v___y_4301_ = v___y_4320_;
v___y_4302_ = v___y_4321_;
v___y_4303_ = v___y_4322_;
goto v___jp_4300_;
}
}
v___jp_4349_:
{
lean_object* v___x_4353_; lean_object* v_env_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4353_ = lean_st_ref_get(v___y_4352_);
v_env_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc_ref(v_env_4354_);
lean_dec(v___x_4353_);
v___x_4355_ = 0;
lean_inc(v_decl_4247_);
v___x_4356_ = l_Lean_Environment_find_x3f(v_env_4354_, v_decl_4247_, v___x_4355_);
if (lean_obj_tag(v___x_4356_) == 0)
{
v___y_4301_ = v_name_4350_;
v___y_4302_ = v___y_4351_;
v___y_4303_ = v___y_4352_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4357_; lean_object* v_env_4358_; uint8_t v___x_4359_; uint8_t v___x_4360_; 
lean_dec_ref_known(v___x_4356_, 1);
v___x_4357_ = lean_st_ref_get(v___y_4352_);
v_env_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc_ref(v_env_4358_);
lean_dec(v___x_4357_);
v___x_4359_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4358_, v_decl_4247_);
v___x_4360_ = lean_bool_not(v___x_4359_);
if (v___x_4360_ == 0)
{
v___y_4319_ = v___x_4355_;
v___y_4320_ = v_name_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
goto v___jp_4318_;
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
lean_dec_ref(v_name_4350_);
lean_dec(v___x_4242_);
v___x_4361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4362_ = l_Lean_MessageData_ofConstName(v_decl_4247_, v___x_4355_);
v___x_4363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
v___x_4364_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4248_, v___x_4365_, v___y_4351_, v___y_4352_);
lean_dec(v_stx_4248_);
return v___x_4366_;
}
}
}
v___jp_4367_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4368_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4369_ = l_Lean_Name_mkStr4(v___x_4243_, v___x_4244_, v___x_4368_, v___x_4245_);
lean_inc(v_stx_4248_);
v___x_4370_ = l_Lean_Syntax_isOfKind(v_stx_4248_, v___x_4369_);
lean_dec(v___x_4369_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_stx_4248_);
lean_dec(v_decl_4247_);
lean_dec(v___x_4242_);
v___x_4371_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4372_ = l_Lean_MessageData_ofName(v_name_4246_);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4375_, v___y_4250_, v___y_4251_);
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4376_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4376_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
else
{
lean_object* v___x_4385_; lean_object* v_name_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4385_ = lean_unsigned_to_nat(1u);
v_name_4386_ = l_Lean_Syntax_getArg(v_stx_4248_, v___x_4385_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4386_);
v___x_4388_ = l_Lean_Syntax_isOfKind(v_name_4386_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4386_);
v___x_4390_ = l_Lean_Syntax_isOfKind(v_name_4386_, v___x_4389_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v_name_4386_);
lean_dec(v_stx_4248_);
lean_dec(v_decl_4247_);
lean_dec(v___x_4242_);
v___x_4391_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4392_ = l_Lean_MessageData_ofName(v_name_4246_);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4395_, v___y_4250_, v___y_4251_);
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
lean_dec(v_name_4246_);
v___x_4405_ = l_Lean_TSyntax_getId(v_name_4386_);
lean_dec(v_name_4386_);
v___x_4406_ = l_Lean_Name_toString(v___x_4405_, v___x_4388_);
v_name_4350_ = v___x_4406_;
v___y_4351_ = v___y_4250_;
v___y_4352_ = v___y_4251_;
goto v___jp_4349_;
}
}
else
{
lean_object* v___x_4407_; 
lean_dec(v_name_4246_);
v___x_4407_ = l_Lean_TSyntax_getString(v_name_4386_);
lean_dec(v_name_4386_);
v_name_4350_ = v___x_4407_;
v___y_4351_ = v___y_4250_;
v___y_4352_ = v___y_4251_;
goto v___jp_4349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v___x_4411_, lean_object* v___x_4412_, lean_object* v___x_4413_, lean_object* v___x_4414_, lean_object* v_name_4415_, lean_object* v_decl_4416_, lean_object* v_stx_4417_, lean_object* v_kind_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v_kind_boxed_4422_; lean_object* v_res_4423_; 
v_kind_boxed_4422_ = lean_unbox(v_kind_4418_);
v_res_4423_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(v___x_4411_, v___x_4412_, v___x_4413_, v___x_4414_, v_name_4415_, v_decl_4416_, v_stx_4417_, v_kind_boxed_4422_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
return v_res_4423_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = lean_unsigned_to_nat(3374007381u);
v___x_4436_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4437_ = l_Lean_Name_num___override(v___x_4436_, v___x_4435_);
return v___x_4437_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4439_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4440_ = l_Lean_Name_str___override(v___x_4439_, v___x_4438_);
return v___x_4440_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4442_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4443_ = l_Lean_Name_str___override(v___x_4442_, v___x_4441_);
return v___x_4443_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = lean_unsigned_to_nat(2u);
v___x_4445_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4446_ = l_Lean_Name_num___override(v___x_4445_, v___x_4444_);
return v___x_4446_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4448_; lean_object* v___x_4449_; lean_object* v_name_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4448_ = 2;
v___x_4449_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v_name_4450_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4451_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4452_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v_name_4450_);
lean_ctor_set(v___x_4452_, 2, v___x_4449_);
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*3, v___x_4448_);
return v___x_4452_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4453_; lean_object* v___f_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___f_4453_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___f_4454_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4455_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
lean_ctor_set(v___x_4456_, 1, v___f_4454_);
lean_ctor_set(v___x_4456_, 2, v___f_4453_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4459_ = l_Lean_registerBuiltinAttribute(v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object* v_tac_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4462_, v___y_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tac_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(v_tac_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4472_, lean_object* v_k_4473_, lean_object* v_x_4474_, lean_object* v_x_4475_, lean_object* v_x_4476_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4472_, v_k_4473_, v_x_4474_, v_x_4475_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4478_, lean_object* v_k_4479_, lean_object* v_x_4480_, lean_object* v_x_4481_, lean_object* v_x_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(v_as_4478_, v_k_4479_, v_x_4480_, v_x_4481_, v_x_4482_);
lean_dec_ref(v_k_4479_);
lean_dec_ref(v_as_4478_);
return v_res_4483_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0));
v___x_4486_ = l_Lean_stringToMessageData(v___x_4485_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object* v_catName_4487_, lean_object* v_declName_4488_, uint8_t v___builtIn_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; uint8_t v___x_4494_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4520_; lean_object* v___y_4521_; uint8_t v___y_4522_; lean_object* v___y_4531_; lean_object* v___y_4532_; 
v___x_4493_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_4494_ = lean_name_eq(v_catName_4487_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4544_; lean_object* v_env_4552_; lean_object* v___x_4553_; 
v___x_4544_ = lean_st_ref_get(v___y_4491_);
v_env_4552_ = lean_ctor_get(v___x_4544_, 0);
lean_inc_ref(v_env_4552_);
lean_dec(v___x_4544_);
lean_inc(v_declName_4488_);
v___x_4553_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4552_, v_declName_4488_);
if (lean_obj_tag(v___x_4553_) == 0)
{
if (v___x_4494_ == 0)
{
v___y_4531_ = v___y_4490_;
v___y_4532_ = v___y_4491_;
goto v___jp_4530_;
}
else
{
goto v___jp_4545_;
}
}
else
{
lean_dec_ref_known(v___x_4553_, 1);
goto v___jp_4545_;
}
v___jp_4545_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4547_ = l_Lean_MessageData_ofConstName(v_declName_4488_, v___x_4494_);
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
v___x_4549_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4548_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4550_, v___y_4490_, v___y_4491_);
return v___x_4551_;
}
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
lean_dec(v_declName_4488_);
v___x_4554_ = lean_box(0);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
v___jp_4495_:
{
lean_object* v___x_4498_; lean_object* v_env_4499_; lean_object* v___x_4500_; lean_object* v_toEnvExtension_4501_; lean_object* v_asyncMode_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4498_ = lean_st_ref_get(v___y_4497_);
v_env_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc_ref(v_env_4499_);
lean_dec(v___x_4498_);
v___x_4500_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4501_ = lean_ctor_get(v___x_4500_, 0);
v_asyncMode_4502_ = lean_ctor_get(v_toEnvExtension_4501_, 2);
v___x_4503_ = lean_box(1);
v___x_4504_ = lean_box(0);
v___x_4505_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4503_, v___x_4500_, v_env_4499_, v_asyncMode_4502_, v___x_4504_);
v___x_4506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4505_, v_declName_4488_);
lean_dec(v___x_4505_);
if (lean_obj_tag(v___x_4506_) == 1)
{
lean_object* v_val_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v_val_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_val_4507_);
lean_dec_ref_known(v___x_4506_, 1);
v___x_4508_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4509_ = l_Lean_MessageData_ofConstName(v_declName_4488_, v___x_4494_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1);
v___x_4512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4510_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
v___x_4513_ = l_Lean_stringToMessageData(v_val_4507_);
v___x_4514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4512_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
v___x_4515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
lean_ctor_set(v___x_4515_, 1, v___x_4508_);
v___x_4516_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4515_, v___y_4496_, v___y_4497_);
return v___x_4516_;
}
else
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
lean_dec(v___x_4506_);
lean_dec(v_declName_4488_);
v___x_4517_ = lean_box(0);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
v___jp_4519_:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_bool_not(v___y_4522_);
if (v___x_4523_ == 0)
{
v___y_4496_ = v___y_4520_;
v___y_4497_ = v___y_4521_;
goto v___jp_4495_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4525_ = l_Lean_MessageData_ofConstName(v_declName_4488_, v___x_4494_);
v___x_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4524_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4526_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4528_, v___y_4520_, v___y_4521_);
return v___x_4529_;
}
}
v___jp_4530_:
{
lean_object* v___x_4533_; lean_object* v_env_4534_; lean_object* v___x_4535_; lean_object* v_toEnvExtension_4536_; lean_object* v_asyncMode_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4533_ = lean_st_ref_get(v___y_4532_);
v_env_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc_ref(v_env_4534_);
lean_dec(v___x_4533_);
v___x_4535_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4536_ = lean_ctor_get(v___x_4535_, 0);
v_asyncMode_4537_ = lean_ctor_get(v_toEnvExtension_4536_, 2);
v___x_4538_ = lean_box(1);
v___x_4539_ = lean_box(0);
v___x_4540_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4538_, v___x_4535_, v_env_4534_, v_asyncMode_4537_, v___x_4539_);
v___x_4541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4540_, v_declName_4488_);
lean_dec(v___x_4540_);
if (lean_obj_tag(v___x_4541_) == 1)
{
lean_object* v_val_4542_; 
v_val_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_val_4542_);
lean_dec_ref_known(v___x_4541_, 1);
if (lean_obj_tag(v_val_4542_) == 0)
{
lean_dec_ref_known(v_val_4542_, 5);
v___y_4520_ = v___y_4531_;
v___y_4521_ = v___y_4532_;
v___y_4522_ = v___x_4494_;
goto v___jp_4519_;
}
else
{
uint8_t v___x_4543_; 
v___x_4543_ = 1;
v___y_4520_ = v___y_4531_;
v___y_4521_ = v___y_4532_;
v___y_4522_ = v___x_4543_;
goto v___jp_4519_;
}
}
else
{
lean_dec(v___x_4541_);
v___y_4496_ = v___y_4531_;
v___y_4497_ = v___y_4532_;
goto v___jp_4495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object* v_catName_4556_, lean_object* v_declName_4557_, lean_object* v___builtIn_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
uint8_t v___builtIn_boxed_4562_; lean_object* v_res_4563_; 
v___builtIn_boxed_4562_ = lean_unbox(v___builtIn_4558_);
v_res_4563_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(v_catName_4556_, v_declName_4557_, v___builtIn_boxed_4562_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v_catName_4556_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4567_; lean_object* v___x_4568_; 
v___f_4567_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0));
v___x_4568_ = l_Lean_Parser_registerParserAttributeHook(v___f_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
return v_res_4570_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
