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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1;
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_16_; size_t v___x_17_; size_t v___x_18_; 
v___x_16_ = ((size_t)5ULL);
v___x_17_ = ((size_t)1ULL);
v___x_18_ = lean_usize_shift_left(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; 
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__0);
v___x_21_ = lean_usize_sub(v___x_20_, v___x_19_);
return v___x_21_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(lean_object* v_x_22_, size_t v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v_es_25_; lean_object* v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v___x_29_; lean_object* v_j_30_; lean_object* v___x_31_; 
v_es_25_ = lean_ctor_get(v_x_22_, 0);
v___x_26_ = lean_box(2);
v___x_27_ = ((size_t)5ULL);
v___x_28_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1);
v___x_29_ = lean_usize_land(v_x_23_, v___x_28_);
v_j_30_ = lean_usize_to_nat(v___x_29_);
v___x_31_ = lean_array_get_borrowed(v___x_26_, v_es_25_, v_j_30_);
lean_dec(v_j_30_);
switch(lean_obj_tag(v___x_31_))
{
case 0:
{
lean_object* v_key_32_; uint8_t v___x_33_; 
v_key_32_ = lean_ctor_get(v___x_31_, 0);
v___x_33_ = lean_name_eq(v_x_24_, v_key_32_);
return v___x_33_;
}
case 1:
{
lean_object* v_node_34_; size_t v___x_35_; 
v_node_34_ = lean_ctor_get(v___x_31_, 0);
v___x_35_ = lean_usize_shift_right(v_x_23_, v___x_27_);
v_x_22_ = v_node_34_;
v_x_23_ = v___x_35_;
goto _start;
}
default: 
{
uint8_t v___x_37_; 
v___x_37_ = 0;
return v___x_37_;
}
}
}
else
{
lean_object* v_ks_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_ks_38_ = lean_ctor_get(v_x_22_, 0);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_ks_38_, v___x_39_, v_x_24_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___boxed(lean_object* v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
size_t v_x_375__boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_x_375__boxed_44_ = lean_unbox_usize(v_x_42_);
lean_dec(v_x_42_);
v_res_45_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_41_, v_x_375__boxed_44_, v_x_43_);
lean_dec(v_x_43_);
lean_dec_ref(v_x_41_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_47_; uint64_t v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1723u);
v___x_48_ = lean_uint64_of_nat(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint64_t v___y_52_; 
if (lean_obj_tag(v_x_50_) == 0)
{
uint64_t v___x_55_; 
v___x_55_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_52_ = v___x_55_;
goto v___jp_51_;
}
else
{
uint64_t v_hash_56_; 
v_hash_56_ = lean_ctor_get_uint64(v_x_50_, sizeof(void*)*2);
v___y_52_ = v_hash_56_;
goto v___jp_51_;
}
v___jp_51_:
{
size_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_uint64_to_usize(v___y_52_);
v___x_54_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_49_, v___x_53_, v_x_50_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec_ref(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_61_, lean_object* v_vals_62_, lean_object* v_i_63_, lean_object* v_k_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_get_size(v_keys_61_);
v___x_66_ = lean_nat_dec_lt(v_i_63_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_dec(v_i_63_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v_k_x27_68_; uint8_t v___x_69_; 
v_k_x27_68_ = lean_array_fget_borrowed(v_keys_61_, v_i_63_);
v___x_69_ = lean_name_eq(v_k_64_, v_k_x27_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_i_63_, v___x_70_);
lean_dec(v_i_63_);
v_i_63_ = v___x_71_;
goto _start;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_array_fget_borrowed(v_vals_62_, v_i_63_);
lean_dec(v_i_63_);
lean_inc(v___x_73_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_75_, lean_object* v_vals_76_, lean_object* v_i_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_75_, v_vals_76_, v_i_77_, v_k_78_);
lean_dec(v_k_78_);
lean_dec_ref(v_vals_76_);
lean_dec_ref(v_keys_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(lean_object* v_x_80_, size_t v_x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_es_83_; lean_object* v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v_j_88_; lean_object* v___x_89_; 
v_es_83_ = lean_ctor_get(v_x_80_, 0);
v___x_84_ = lean_box(2);
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1);
v___x_87_ = lean_usize_land(v_x_81_, v___x_86_);
v_j_88_ = lean_usize_to_nat(v___x_87_);
v___x_89_ = lean_array_get_borrowed(v___x_84_, v_es_83_, v_j_88_);
lean_dec(v_j_88_);
switch(lean_obj_tag(v___x_89_))
{
case 0:
{
lean_object* v_key_90_; lean_object* v_val_91_; uint8_t v___x_92_; 
v_key_90_ = lean_ctor_get(v___x_89_, 0);
v_val_91_ = lean_ctor_get(v___x_89_, 1);
v___x_92_ = lean_name_eq(v_x_82_, v_key_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
lean_inc(v_val_91_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_val_91_);
return v___x_94_;
}
}
case 1:
{
lean_object* v_node_95_; size_t v___x_96_; 
v_node_95_ = lean_ctor_get(v___x_89_, 0);
v___x_96_ = lean_usize_shift_right(v_x_81_, v___x_85_);
v_x_80_ = v_node_95_;
v_x_81_ = v___x_96_;
goto _start;
}
default: 
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
}
else
{
lean_object* v_ks_99_; lean_object* v_vs_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_ks_99_ = lean_ctor_get(v_x_80_, 0);
v_vs_100_ = lean_ctor_get(v_x_80_, 1);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_ks_99_, v_vs_100_, v___x_101_, v_x_82_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg___boxed(lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
size_t v_x_468__boxed_106_; lean_object* v_res_107_; 
v_x_468__boxed_106_ = lean_unbox_usize(v_x_104_);
lean_dec(v_x_104_);
v_res_107_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_103_, v_x_468__boxed_106_, v_x_105_);
lean_dec(v_x_105_);
lean_dec_ref(v_x_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint64_t v___y_111_; 
if (lean_obj_tag(v_x_109_) == 0)
{
uint64_t v___x_114_; 
v___x_114_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_111_ = v___x_114_;
goto v___jp_110_;
}
else
{
uint64_t v_hash_115_; 
v_hash_115_ = lean_ctor_get_uint64(v_x_109_, sizeof(void*)*2);
v___y_111_ = v_hash_115_;
goto v___jp_110_;
}
v___jp_110_:
{
size_t v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_uint64_to_usize(v___y_111_);
v___x_113_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_108_, v___x_112_, v_x_109_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec_ref(v_x_116_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object* v_env_122_, lean_object* v_kind_123_){
_start:
{
lean_object* v___x_124_; lean_object* v_ext_125_; lean_object* v_toEnvExtension_126_; lean_object* v_asyncMode_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_categories_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_124_ = l_Lean_Parser_parserExtension;
v_ext_125_ = lean_ctor_get(v___x_124_, 1);
v_toEnvExtension_126_ = lean_ctor_get(v_ext_125_, 0);
v_asyncMode_127_ = lean_ctor_get(v_toEnvExtension_126_, 2);
v___x_128_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_129_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_128_, v___x_124_, v_env_122_, v_asyncMode_127_);
v_categories_130_ = lean_ctor_get(v___x_129_, 2);
lean_inc_ref(v_categories_130_);
lean_dec(v___x_129_);
v___x_131_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_132_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_categories_130_, v___x_131_);
lean_dec_ref(v_categories_130_);
if (lean_obj_tag(v___x_132_) == 1)
{
lean_object* v_val_133_; lean_object* v_kinds_134_; uint8_t v___x_135_; 
v_val_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_133_);
lean_dec_ref(v___x_132_);
v_kinds_134_ = lean_ctor_get(v_val_133_, 1);
lean_inc_ref(v_kinds_134_);
lean_dec(v_val_133_);
v___x_135_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_134_, v_kind_123_);
lean_dec_ref(v_kinds_134_);
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
lean_dec(v___x_132_);
v___x_136_ = 0;
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_isTactic___boxed(lean_object* v_env_137_, lean_object* v_kind_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_137_, v_kind_138_);
lean_dec(v_kind_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(lean_object* v_00_u03b2_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___boxed(lean_object* v_00_u03b2_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(v_00_u03b2_145_, v_x_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec_ref(v_x_146_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(lean_object* v_00_u03b2_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_150_, v_x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___boxed(lean_object* v_00_u03b2_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(v_00_u03b2_153_, v_x_154_, v_x_155_);
lean_dec(v_x_155_);
lean_dec_ref(v_x_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(lean_object* v_00_u03b2_158_, lean_object* v_x_159_, size_t v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_159_, v_x_160_, v_x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___boxed(lean_object* v_00_u03b2_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
size_t v_x_577__boxed_167_; lean_object* v_res_168_; 
v_x_577__boxed_167_ = lean_unbox_usize(v_x_165_);
lean_dec(v_x_165_);
v_res_168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(v_00_u03b2_163_, v_x_164_, v_x_577__boxed_167_, v_x_166_);
lean_dec(v_x_166_);
lean_dec_ref(v_x_164_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(lean_object* v_00_u03b2_169_, lean_object* v_x_170_, size_t v_x_171_, lean_object* v_x_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_170_, v_x_171_, v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___boxed(lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
size_t v_x_588__boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_588__boxed_178_ = lean_unbox_usize(v_x_176_);
lean_dec(v_x_176_);
v_res_179_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(v_00_u03b2_174_, v_x_175_, v_x_588__boxed_178_, v_x_177_);
lean_dec(v_x_177_);
lean_dec_ref(v_x_175_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_181_, lean_object* v_keys_182_, lean_object* v_vals_183_, lean_object* v_heq_184_, lean_object* v_i_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_182_, v_vals_183_, v_i_185_, v_k_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_188_, lean_object* v_keys_189_, lean_object* v_vals_190_, lean_object* v_heq_191_, lean_object* v_i_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(v_00_u03b2_188_, v_keys_189_, v_vals_190_, v_heq_191_, v_i_192_, v_k_193_);
lean_dec(v_k_193_);
lean_dec_ref(v_vals_190_);
lean_dec_ref(v_keys_189_);
return v_res_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_195_, lean_object* v_keys_196_, lean_object* v_vals_197_, lean_object* v_heq_198_, lean_object* v_i_199_, lean_object* v_k_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_keys_196_, v_i_199_, v_k_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_202_, lean_object* v_keys_203_, lean_object* v_vals_204_, lean_object* v_heq_205_, lean_object* v_i_206_, lean_object* v_k_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(v_00_u03b2_202_, v_keys_203_, v_vals_204_, v_heq_205_, v_i_206_, v_k_207_);
lean_dec(v_k_207_);
lean_dec_ref(v_vals_204_);
lean_dec_ref(v_keys_203_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_as_210_, lean_object* v_x_211_){
_start:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_214_; 
v_fst_212_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v_x_211_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v_x_211_);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_212_, v_snd_213_, v_as_210_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_215_, lean_object* v_pivot_216_, lean_object* v_as_217_, lean_object* v_i_218_, lean_object* v_k_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = lean_nat_dec_lt(v_k_219_, v_hi_215_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_k_219_);
v___x_221_ = lean_array_fswap(v_as_217_, v_i_218_, v_hi_215_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_i_218_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_fst_224_; lean_object* v_fst_225_; uint8_t v___x_226_; 
v___x_223_ = lean_array_fget_borrowed(v_as_217_, v_k_219_);
v_fst_224_ = lean_ctor_get(v___x_223_, 0);
v_fst_225_ = lean_ctor_get(v_pivot_216_, 0);
v___x_226_ = l_Lean_Name_quickLt(v_fst_224_, v_fst_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_k_219_, v___x_227_);
lean_dec(v_k_219_);
v_k_219_ = v___x_228_;
goto _start;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_array_fswap(v_as_217_, v_i_218_, v_k_219_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_i_218_, v___x_231_);
lean_dec(v_i_218_);
v___x_233_ = lean_nat_add(v_k_219_, v___x_231_);
lean_dec(v_k_219_);
v_as_217_ = v___x_230_;
v_i_218_ = v___x_232_;
v_k_219_ = v___x_233_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_235_, lean_object* v_pivot_236_, lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_k_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_235_, v_pivot_236_, v_as_237_, v_i_238_, v_k_239_);
lean_dec_ref(v_pivot_236_);
lean_dec(v_hi_235_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_241_, lean_object* v_x2_242_){
_start:
{
lean_object* v_fst_243_; lean_object* v_fst_244_; uint8_t v___x_245_; 
v_fst_243_ = lean_ctor_get(v_x1_241_, 0);
v_fst_244_ = lean_ctor_get(v_x2_242_, 0);
v___x_245_ = l_Lean_Name_quickLt(v_fst_243_, v_fst_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_246_, lean_object* v_x2_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_246_, v_x2_247_);
lean_dec_ref(v_x2_247_);
lean_dec_ref(v_x1_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_250_, lean_object* v_as_251_, lean_object* v_lo_252_, lean_object* v_hi_253_){
_start:
{
lean_object* v___y_255_; uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_lt(v_lo_252_, v_hi_253_);
if (v___x_265_ == 0)
{
lean_dec(v_lo_252_);
return v_as_251_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_mid_268_; lean_object* v___y_270_; lean_object* v___y_276_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_266_ = lean_nat_add(v_lo_252_, v_hi_253_);
v___x_267_ = lean_unsigned_to_nat(1u);
v_mid_268_ = lean_nat_shiftr(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
v___x_281_ = lean_array_fget_borrowed(v_as_251_, v_mid_268_);
v___x_282_ = lean_array_fget_borrowed(v_as_251_, v_lo_252_);
v___x_283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
v___y_276_ = v_as_251_;
goto v___jp_275_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_fswap(v_as_251_, v_lo_252_, v_mid_268_);
v___y_276_ = v___x_284_;
goto v___jp_275_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_array_fget_borrowed(v___y_270_, v_mid_268_);
v___x_272_ = lean_array_fget_borrowed(v___y_270_, v_hi_253_);
v___x_273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_mid_268_);
v___y_255_ = v___y_270_;
goto v___jp_254_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_array_fswap(v___y_270_, v_mid_268_, v_hi_253_);
lean_dec(v_mid_268_);
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_array_fget_borrowed(v___y_276_, v_hi_253_);
v___x_278_ = lean_array_fget_borrowed(v___y_276_, v_lo_252_);
v___x_279_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
v___y_270_ = v___y_276_;
goto v___jp_269_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_array_fswap(v___y_276_, v_lo_252_, v_hi_253_);
v___y_270_ = v___x_280_;
goto v___jp_269_;
}
}
}
v___jp_254_:
{
lean_object* v_pivot_256_; lean_object* v___x_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; uint8_t v___x_260_; 
v_pivot_256_ = lean_array_fget(v___y_255_, v_hi_253_);
lean_inc_n(v_lo_252_, 2);
v___x_257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_253_, v_pivot_256_, v___y_255_, v_lo_252_, v_lo_252_);
lean_dec(v_pivot_256_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_fst_258_);
v_snd_259_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_snd_259_);
lean_dec_ref(v___x_257_);
v___x_260_ = lean_nat_dec_le(v_hi_253_, v_fst_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_250_, v_snd_259_, v_lo_252_, v_fst_258_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_fst_258_, v___x_262_);
lean_dec(v_fst_258_);
v_as_251_ = v___x_261_;
v_lo_252_ = v___x_263_;
goto _start;
}
else
{
lean_dec(v_fst_258_);
lean_dec(v_lo_252_);
return v_snd_259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_285_, lean_object* v_as_286_, lean_object* v_lo_287_, lean_object* v_hi_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_285_, v_as_286_, v_lo_287_, v_hi_288_);
lean_dec(v_hi_288_);
lean_dec(v_n_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v_l_294_; lean_object* v_r_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_k_292_ = lean_ctor_get(v_x_291_, 1);
v_v_293_ = lean_ctor_get(v_x_291_, 2);
v_l_294_ = lean_ctor_get(v_x_291_, 3);
v_r_295_ = lean_ctor_get(v_x_291_, 4);
v___x_296_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_290_, v_l_294_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_k_292_);
lean_ctor_set(v___x_297_, 1, v_v_293_);
v___x_298_ = lean_array_push(v___x_296_, v___x_297_);
v_init_290_ = v___x_298_;
v_x_291_ = v_r_295_;
goto _start;
}
else
{
return v_init_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_300_, v_x_301_);
lean_dec(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_305_, lean_object* v_s_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___x_316_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_309_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_308_, v_s_306_);
v___x_310_ = lean_array_get_size(v___x_309_);
v___x_316_ = lean_nat_dec_eq(v___x_310_, v___x_307_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___y_320_; uint8_t v___x_322_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_sub(v___x_310_, v___x_317_);
v___x_322_ = lean_nat_dec_le(v___x_307_, v___x_318_);
if (v___x_322_ == 0)
{
lean_inc(v___x_318_);
v___y_320_ = v___x_318_;
goto v___jp_319_;
}
else
{
v___y_320_ = v___x_307_;
goto v___jp_319_;
}
v___jp_319_:
{
uint8_t v___x_321_; 
v___x_321_ = lean_nat_dec_le(v___y_320_, v___x_318_);
if (v___x_321_ == 0)
{
lean_dec(v___x_318_);
lean_inc(v___y_320_);
v___y_312_ = v___y_320_;
v___y_313_ = v___y_320_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___y_320_;
v___y_313_ = v___x_318_;
goto v___jp_311_;
}
}
}
else
{
lean_object* v___x_323_; 
lean_inc_ref_n(v___x_309_, 2);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_309_);
lean_ctor_set(v___x_323_, 1, v___x_309_);
lean_ctor_set(v___x_323_, 2, v___x_309_);
return v___x_323_;
}
v___jp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_310_, v___x_309_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_inc_ref_n(v___x_314_, 2);
v___x_315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_324_, lean_object* v_s_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_324_, v_s_325_);
lean_dec(v_s_325_);
lean_dec_ref(v_x_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_329_);
lean_dec(v_x_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_es_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_334_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_333_, v_es_331_);
v___x_335_ = lean_array_get_size(v___x_334_);
v___x_336_ = lean_nat_dec_eq(v___x_335_, v___x_332_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___y_340_; uint8_t v___x_344_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_sub(v___x_335_, v___x_337_);
v___x_344_ = lean_nat_dec_le(v___x_332_, v___x_338_);
if (v___x_344_ == 0)
{
lean_inc(v___x_338_);
v___y_340_ = v___x_338_;
goto v___jp_339_;
}
else
{
v___y_340_ = v___x_332_;
goto v___jp_339_;
}
v___jp_339_:
{
uint8_t v___x_341_; 
v___x_341_ = lean_nat_dec_le(v___y_340_, v___x_338_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v___x_338_);
lean_inc(v___y_340_);
v___x_342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_335_, v___x_334_, v___y_340_, v___y_340_);
lean_dec(v___y_340_);
return v___x_342_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_335_, v___x_334_, v___y_340_, v___x_338_);
lean_dec(v___x_338_);
return v___x_343_;
}
}
}
else
{
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_es_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_es_345_);
lean_dec(v_es_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_353_, lean_object* v_x_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_353_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_358_, lean_object* v_x_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_358_, v_x_359_, v___y_360_);
lean_dec_ref(v___y_360_);
lean_dec_ref(v_x_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_396_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object* v_init_399_, lean_object* v_t_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_399_, v_t_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_402_, lean_object* v_t_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(v_init_402_, v_t_403_);
lean_dec(v_t_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object* v_n_405_, lean_object* v_as_406_, lean_object* v_lo_407_, lean_object* v_hi_408_, lean_object* v_w_409_, lean_object* v_hlo_410_, lean_object* v_hhi_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_n_405_, v_as_406_, v_lo_407_, v_hi_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_413_, lean_object* v_as_414_, lean_object* v_lo_415_, lean_object* v_hi_416_, lean_object* v_w_417_, lean_object* v_hlo_418_, lean_object* v_hhi_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(v_n_413_, v_as_414_, v_lo_415_, v_hi_416_, v_w_417_, v_hlo_418_, v_hhi_419_);
lean_dec(v_hi_416_);
lean_dec(v_n_413_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_421_, lean_object* v_lo_422_, lean_object* v_hi_423_, lean_object* v_hhi_424_, lean_object* v_pivot_425_, lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_k_428_, lean_object* v_ilo_429_, lean_object* v_ik_430_, lean_object* v_w_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_423_, v_pivot_425_, v_as_426_, v_i_427_, v_k_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_433_, lean_object* v_lo_434_, lean_object* v_hi_435_, lean_object* v_hhi_436_, lean_object* v_pivot_437_, lean_object* v_as_438_, lean_object* v_i_439_, lean_object* v_k_440_, lean_object* v_ilo_441_, lean_object* v_ik_442_, lean_object* v_w_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1_spec__2(v_n_433_, v_lo_434_, v_hi_435_, v_hhi_436_, v_pivot_437_, v_as_438_, v_i_439_, v_k_440_, v_ilo_441_, v_ik_442_, v_w_443_);
lean_dec_ref(v_pivot_437_);
lean_dec(v_hi_435_);
lean_dec(v_lo_434_);
lean_dec(v_n_433_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object* v_as_445_, lean_object* v_k_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_m_451_; lean_object* v_a_452_; uint8_t v___x_453_; 
v___x_449_ = lean_nat_add(v_x_447_, v_x_448_);
v___x_450_ = lean_unsigned_to_nat(1u);
v_m_451_ = lean_nat_shiftr(v___x_449_, v___x_450_);
lean_dec(v___x_449_);
v_a_452_ = lean_array_fget_borrowed(v_as_445_, v_m_451_);
v___x_453_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_452_, v_k_446_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_dec(v_x_448_);
v___x_454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_446_, v_a_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_m_451_);
lean_dec(v_x_447_);
lean_inc(v_a_452_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_a_452_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_m_451_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_nat_sub(v_m_451_, v___x_450_);
lean_dec(v_m_451_);
v___x_459_ = lean_nat_dec_lt(v___x_458_, v_x_447_);
if (v___x_459_ == 0)
{
v_x_448_ = v___x_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_dec(v___x_458_);
lean_dec(v_x_447_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec(v_m_451_);
lean_dec(v_x_447_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
lean_dec(v_x_447_);
v___x_463_ = lean_nat_add(v_m_451_, v___x_450_);
lean_dec(v_m_451_);
v___x_464_ = lean_nat_dec_le(v___x_463_, v_x_448_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v___x_463_);
lean_dec(v_x_448_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
v_x_447_ = v___x_463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object* v_as_467_, lean_object* v_k_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_467_, v_k_468_, v_x_469_, v_x_470_);
lean_dec_ref(v_k_468_);
lean_dec_ref(v_as_467_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object* v_env_472_, lean_object* v_tac_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_box(1);
v___x_475_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_472_, v_tac_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v_toEnvExtension_477_; lean_object* v_asyncMode_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_476_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_477_ = lean_ctor_get(v___x_476_, 0);
v_asyncMode_478_ = lean_ctor_get(v_toEnvExtension_477_, 2);
v___x_479_ = lean_box(0);
v___x_480_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_474_, v___x_476_, v_env_472_, v_asyncMode_478_, v___x_479_);
v___x_481_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_480_, v_tac_473_);
lean_dec(v_tac_473_);
lean_dec(v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_val_482_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v___x_475_);
v___x_483_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v___x_484_ = 0;
v___x_485_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_474_, v___x_483_, v_env_472_, v_val_482_, v___x_484_);
lean_dec(v_val_482_);
lean_dec_ref(v_env_472_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_array_get_size(v___x_485_);
v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v___x_485_);
lean_dec(v_tac_473_);
v___x_489_ = lean_box(0);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_sub(v___x_487_, v___x_490_);
v___x_492_ = lean_nat_dec_le(v___x_486_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v___x_491_);
lean_dec_ref(v___x_485_);
lean_dec(v_tac_473_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_tac_473_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v___x_485_, v___x_495_, v___x_486_, v___x_491_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_485_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
v___x_497_ = lean_box(0);
return v___x_497_;
}
else
{
lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_val_498_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_snd_502_; lean_object* v___x_504_; 
v_snd_502_ = lean_ctor_get(v_val_498_, 1);
lean_inc(v_snd_502_);
lean_dec(v_val_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_snd_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_snd_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(lean_object* v_as_507_, lean_object* v_k_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_507_, v_k_508_, v_x_509_, v_x_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___boxed(lean_object* v_as_513_, lean_object* v_k_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(v_as_513_, v_k_514_, v_x_515_, v_x_516_, v_x_517_);
lean_dec_ref(v_k_514_);
lean_dec_ref(v_as_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0(lean_object* v_toPure_519_, lean_object* v_____do__lift_520_){
_start:
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v_____do__lift_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v_____do__lift_520_);
v___x_522_ = lean_apply_2(v_toPure_519_, lean_box(0), v_a_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(lean_object* v_tac_523_, lean_object* v_toPure_524_, lean_object* v_a_525_, lean_object* v_b_526_, lean_object* v_c_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_name_eq(v_b_526_, v_tac_523_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_a_525_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_c_527_);
v___x_530_ = lean_apply_2(v_toPure_524_, lean_box(0), v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = l_Lean_NameSet_insert(v_c_527_, v_a_525_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = lean_apply_2(v_toPure_524_, lean_box(0), v___x_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed(lean_object* v_tac_534_, lean_object* v_toPure_535_, lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v_c_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(v_tac_534_, v_toPure_535_, v_a_536_, v_b_537_, v_c_538_);
lean_dec(v_b_537_);
lean_dec(v_tac_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(lean_object* v_tac_540_, lean_object* v_toPure_541_, lean_object* v_a_542_, lean_object* v_x_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_fst_545_; lean_object* v_snd_546_; uint8_t v___x_547_; 
v_fst_545_ = lean_ctor_get(v_a_542_, 0);
lean_inc(v_fst_545_);
v_snd_546_ = lean_ctor_get(v_a_542_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v_a_542_);
v___x_547_ = lean_name_eq(v_snd_546_, v_tac_540_);
lean_dec(v_snd_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_fst_545_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___y_544_);
v___x_549_ = lean_apply_2(v_toPure_541_, lean_box(0), v___x_548_);
return v___x_549_;
}
else
{
lean_object* v_found_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_found_550_ = l_Lean_NameSet_insert(v___y_544_, v_fst_545_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_found_550_);
v___x_552_ = lean_apply_2(v_toPure_541_, lean_box(0), v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed(lean_object* v_tac_553_, lean_object* v_toPure_554_, lean_object* v_a_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(v_tac_553_, v_toPure_554_, v_a_555_, v_x_556_, v___y_557_);
lean_dec(v_tac_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3(lean_object* v_toPure_559_, lean_object* v_____s_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_____s_560_);
v___x_562_ = lean_apply_2(v_toPure_559_, lean_box(0), v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4(lean_object* v_inst_563_, lean_object* v___f_564_, lean_object* v_toBind_565_, lean_object* v___f_566_, lean_object* v_a_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_sz_570_ = lean_array_size(v_a_567_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_563_, v_a_567_, v___f_564_, v_sz_570_, v___x_571_, v___y_569_);
v___x_573_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_572_, v___f_566_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5(lean_object* v_toPure_574_, lean_object* v_____s_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_apply_2(v_toPure_574_, lean_box(0), v_____s_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object* v___x_577_, lean_object* v_toEnvExtension_578_, lean_object* v_env_579_, lean_object* v_asyncMode_580_, lean_object* v___x_581_, lean_object* v_inst_582_, lean_object* v___f_583_, lean_object* v_toBind_584_, lean_object* v___f_585_, lean_object* v_____s_586_){
_start:
{
lean_object* v___x_587_; lean_object* v_importedEntries_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_577_, v_toEnvExtension_578_, v_env_579_, v_asyncMode_580_, v___x_581_);
v_importedEntries_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_importedEntries_588_);
lean_dec(v___x_587_);
v_sz_589_ = lean_array_size(v_importedEntries_588_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_582_, v_importedEntries_588_, v___f_583_, v_sz_589_, v___x_590_, v_____s_586_);
v___x_592_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v___x_591_, v___f_585_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object* v___x_593_, lean_object* v_toEnvExtension_594_, lean_object* v_env_595_, lean_object* v_asyncMode_596_, lean_object* v___x_597_, lean_object* v_inst_598_, lean_object* v___f_599_, lean_object* v_toBind_600_, lean_object* v___f_601_, lean_object* v_____s_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(v___x_593_, v_toEnvExtension_594_, v_env_595_, v_asyncMode_596_, v___x_597_, v_inst_598_, v___f_599_, v_toBind_600_, v___f_601_, v_____s_602_);
lean_dec(v_asyncMode_596_);
lean_dec_ref(v_toEnvExtension_594_);
lean_dec_ref(v___x_593_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object* v___x_604_, lean_object* v_inst_605_, lean_object* v___f_606_, lean_object* v_toBind_607_, lean_object* v___f_608_, lean_object* v___x_609_, lean_object* v___f_610_, lean_object* v___f_611_, lean_object* v_env_612_){
_start:
{
lean_object* v___x_613_; lean_object* v_toEnvExtension_614_; lean_object* v_asyncMode_615_; lean_object* v_found_616_; lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_613_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_614_ = lean_ctor_get(v___x_613_, 0);
v_asyncMode_615_ = lean_ctor_get(v_toEnvExtension_614_, 2);
v_found_616_ = l_Lean_NameSet_empty;
v___x_617_ = lean_box(0);
lean_inc_n(v_toBind_607_, 2);
lean_inc_ref(v_inst_605_);
lean_inc(v_asyncMode_615_);
lean_inc_ref(v_env_612_);
lean_inc_ref(v_toEnvExtension_614_);
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_618_, 0, v___x_604_);
lean_closure_set(v___f_618_, 1, v_toEnvExtension_614_);
lean_closure_set(v___f_618_, 2, v_env_612_);
lean_closure_set(v___f_618_, 3, v_asyncMode_615_);
lean_closure_set(v___f_618_, 4, v___x_617_);
lean_closure_set(v___f_618_, 5, v_inst_605_);
lean_closure_set(v___f_618_, 6, v___f_606_);
lean_closure_set(v___f_618_, 7, v_toBind_607_);
lean_closure_set(v___f_618_, 8, v___f_608_);
v___x_619_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_609_, v___x_613_, v_env_612_, v_asyncMode_615_, v___x_617_);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_605_, v___f_610_, v_found_616_, v___x_619_);
v___x_621_ = lean_apply_4(v_toBind_607_, lean_box(0), lean_box(0), v___x_620_, v___f_611_);
v___x_622_ = lean_apply_4(v_toBind_607_, lean_box(0), lean_box(0), v___x_621_, v___f_618_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(1);
v___x_624_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_tac_627_){
_start:
{
lean_object* v_toApplicative_628_; lean_object* v_toBind_629_; lean_object* v_getEnv_630_; lean_object* v_toPure_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; 
v_toApplicative_628_ = lean_ctor_get(v_inst_625_, 0);
v_toBind_629_ = lean_ctor_get(v_inst_625_, 1);
lean_inc_n(v_toBind_629_, 3);
v_getEnv_630_ = lean_ctor_get(v_inst_626_, 0);
lean_inc(v_getEnv_630_);
lean_dec_ref(v_inst_626_);
v_toPure_631_ = lean_ctor_get(v_toApplicative_628_, 1);
v___x_632_ = lean_box(1);
v___x_633_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_631_, 5);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_634_, 0, v_toPure_631_);
lean_inc(v_tac_627_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_635_, 0, v_tac_627_);
lean_closure_set(v___f_635_, 1, v_toPure_631_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_636_, 0, v_tac_627_);
lean_closure_set(v___f_636_, 1, v_toPure_631_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_637_, 0, v_toPure_631_);
lean_inc_ref(v_inst_625_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4), 7, 4);
lean_closure_set(v___f_638_, 0, v_inst_625_);
lean_closure_set(v___f_638_, 1, v___f_636_);
lean_closure_set(v___f_638_, 2, v_toBind_629_);
lean_closure_set(v___f_638_, 3, v___f_637_);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5), 2, 1);
lean_closure_set(v___f_639_, 0, v_toPure_631_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7), 9, 8);
lean_closure_set(v___f_640_, 0, v___x_633_);
lean_closure_set(v___f_640_, 1, v_inst_625_);
lean_closure_set(v___f_640_, 2, v___f_638_);
lean_closure_set(v___f_640_, 3, v_toBind_629_);
lean_closure_set(v___f_640_, 4, v___f_639_);
lean_closure_set(v___f_640_, 5, v___x_632_);
lean_closure_set(v___f_640_, 6, v___f_635_);
lean_closure_set(v___f_640_, 7, v___f_634_);
v___x_641_ = lean_apply_4(v_toBind_629_, lean_box(0), lean_box(0), v_getEnv_630_, v___f_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object* v_m_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_tac_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Parser_Tactic_Doc_aliases___redArg(v_inst_643_, v_inst_644_, v_tac_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_647_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_652_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_unsigned_to_nat(32u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_661_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_657_);
lean_ctor_set(v___x_661_, 3, v___x_657_);
lean_ctor_set_usize(v___x_661_, 4, v___x_656_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_box(1);
v___x_663_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_664_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_env_671_; lean_object* v_options_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_env_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_env_671_);
lean_dec(v___x_670_);
v_options_672_ = lean_ctor_get(v___y_667_, 2);
v___x_673_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_674_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_672_);
v___x_675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_675_, 0, v_env_671_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
lean_ctor_set(v___x_675_, 3, v_options_672_);
v___x_676_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_msgData_666_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msgData_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_ref_687_ = lean_ctor_get(v___y_684_, 5);
v___x_688_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_683_, v___y_684_, v___y_685_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_697_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_inc(v_ref_687_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_687_);
lean_ctor_set(v___x_693_, 1, v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_name_709_, lean_object* v_decl_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_714_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_715_ = l_Lean_MessageData_ofName(v_name_709_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_718_, v___y_711_, v___y_712_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_name_720_, lean_object* v_decl_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_name_720_, v_decl_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v_decl_721_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_decl_726_, lean_object* v_x_727_, lean_object* v_____s_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_snd_732_; lean_object* v_fst_733_; lean_object* v_kinds_734_; uint8_t v___x_735_; 
v_snd_732_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_snd_732_);
v_fst_733_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_fst_733_);
lean_dec_ref(v_x_727_);
v_kinds_734_ = lean_ctor_get(v_snd_732_, 1);
lean_inc_ref(v_kinds_734_);
lean_dec(v_snd_732_);
v___x_735_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_734_, v_decl_726_);
lean_dec_ref(v_kinds_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_fst_733_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_____s_728_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_array_push(v_____s_728_, v_fst_733_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_decl_741_, lean_object* v_x_742_, lean_object* v_____s_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_decl_741_, v_x_742_, v_____s_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v_decl_741_);
return v_res_747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(size_t v_sz_751_, size_t v_i_752_, lean_object* v_bs_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_752_, v_sz_751_);
if (v___x_754_ == 0)
{
return v_bs_753_;
}
else
{
lean_object* v_v_755_; lean_object* v___x_756_; lean_object* v_bs_x27_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v_v_755_ = lean_array_uget(v_bs_753_, v_i_752_);
v___x_756_ = lean_unsigned_to_nat(0u);
v_bs_x27_757_ = lean_array_uset(v_bs_753_, v_i_752_, v___x_756_);
v___x_758_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_759_ = l_Lean_MessageData_ofName(v_v_755_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_758_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_752_, v___x_762_);
v___x_764_ = lean_array_uset(v_bs_x27_757_, v_i_752_, v___x_761_);
v_i_752_ = v___x_763_;
v_bs_753_ = v___x_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___boxed(lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_bs_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_770_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_boxed_769_, v_i_boxed_770_, v_bs_768_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(lean_object* v_name_781_, uint8_t v_kind_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___y_792_; 
v___x_786_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1);
v___x_787_ = l_Lean_MessageData_ofName(v_name_781_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
switch(v_kind_782_)
{
case 0:
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4));
v___y_792_ = v___x_799_;
goto v___jp_791_;
}
case 1:
{
lean_object* v___x_800_; 
v___x_800_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5));
v___y_792_ = v___x_800_;
goto v___jp_791_;
}
default: 
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6));
v___y_792_ = v___x_801_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc_ref(v___y_792_);
v___x_793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_793_, 0, v___y_792_);
v___x_794_ = l_Lean_MessageData_ofFormat(v___x_793_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_790_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_797_, v___y_783_, v___y_784_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___boxed(lean_object* v_name_802_, lean_object* v_kind_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
uint8_t v_kind_boxed_807_; lean_object* v_res_808_; 
v_kind_boxed_807_ = lean_unbox(v_kind_803_);
v_res_808_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_802_, v_kind_boxed_807_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(lean_object* v_f_809_, lean_object* v_keys_810_, lean_object* v_vals_811_, lean_object* v_i_812_, lean_object* v_acc_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_get_size(v_keys_810_);
v___x_818_ = lean_nat_dec_lt(v_i_812_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v_i_812_);
lean_dec_ref(v_f_809_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_acc_813_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
else
{
lean_object* v_k_821_; lean_object* v_v_822_; lean_object* v___x_823_; 
v_k_821_ = lean_array_fget_borrowed(v_keys_810_, v_i_812_);
v_v_822_ = lean_array_fget_borrowed(v_vals_811_, v_i_812_);
lean_inc_ref(v_f_809_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v_v_822_);
lean_inc(v_k_821_);
v___x_823_ = lean_apply_6(v_f_809_, v_acc_813_, v_k_821_, v_v_822_, v___y_814_, v___y_815_, lean_box(0));
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
if (lean_obj_tag(v_a_824_) == 0)
{
lean_dec_ref(v_a_824_);
lean_dec(v_i_812_);
lean_dec_ref(v_f_809_);
return v___x_823_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec_ref(v___x_823_);
v_a_825_ = lean_ctor_get(v_a_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref(v_a_824_);
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_add(v_i_812_, v___x_826_);
lean_dec(v_i_812_);
v_i_812_ = v___x_827_;
v_acc_813_ = v_a_825_;
goto _start;
}
}
else
{
lean_dec(v_i_812_);
lean_dec_ref(v_f_809_);
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_f_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_i_832_, lean_object* v_acc_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_829_, v_keys_830_, v_vals_831_, v_i_832_, v_acc_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_vals_831_);
lean_dec_ref(v_keys_830_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_f_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v_es_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_866_; 
v_es_844_ = lean_ctor_get(v_x_839_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_839_);
if (v_isSharedCheck_866_ == 0)
{
v___x_846_ = v_x_839_;
v_isShared_847_ = v_isSharedCheck_866_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_es_844_);
lean_dec(v_x_839_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_866_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_es_844_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_852_; 
lean_dec_ref(v_es_844_);
lean_dec_ref(v_f_838_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 0, v_x_840_);
v___x_852_ = v___x_846_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_x_840_);
v___x_852_ = v_reuseFailAlloc_854_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
else
{
uint8_t v___x_855_; 
v___x_855_ = lean_nat_dec_le(v___x_849_, v___x_849_);
if (v___x_855_ == 0)
{
if (v___x_850_ == 0)
{
lean_object* v___x_857_; 
lean_dec_ref(v_es_844_);
lean_dec_ref(v_f_838_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 0, v_x_840_);
v___x_857_ = v___x_846_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_x_840_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
lean_del_object(v___x_846_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_849_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_838_, v_es_844_, v___x_860_, v___x_861_, v_x_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_es_844_);
return v___x_862_;
}
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
lean_del_object(v___x_846_);
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_849_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_838_, v_es_844_, v___x_863_, v___x_864_, v_x_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_es_844_);
return v___x_865_;
}
}
}
}
else
{
lean_object* v_ks_867_; lean_object* v_vs_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_ks_867_ = lean_ctor_get(v_x_839_, 0);
lean_inc_ref(v_ks_867_);
v_vs_868_ = lean_ctor_get(v_x_839_, 1);
lean_inc_ref(v_vs_868_);
lean_dec_ref(v_x_839_);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_838_, v_ks_867_, v_vs_868_, v___x_869_, v_x_840_, v___y_841_, v___y_842_);
lean_dec_ref(v_vs_868_);
lean_dec_ref(v_ks_867_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(lean_object* v_f_871_, lean_object* v_as_872_, size_t v_i_873_, size_t v_stop_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_a_880_; lean_object* v___y_885_; uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_eq(v_i_873_, v_stop_874_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_array_uget_borrowed(v_as_872_, v_i_873_);
switch(lean_obj_tag(v___x_889_))
{
case 0:
{
lean_object* v_key_890_; lean_object* v_val_891_; lean_object* v___x_892_; 
v_key_890_ = lean_ctor_get(v___x_889_, 0);
v_val_891_ = lean_ctor_get(v___x_889_, 1);
lean_inc_ref(v_f_871_);
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v_val_891_);
lean_inc(v_key_890_);
v___x_892_ = lean_apply_6(v_f_871_, v_b_875_, v_key_890_, v_val_891_, v___y_876_, v___y_877_, lean_box(0));
v___y_885_ = v___x_892_;
goto v___jp_884_;
}
case 1:
{
lean_object* v_node_893_; lean_object* v___x_894_; 
v_node_893_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_node_893_);
lean_inc_ref(v_f_871_);
v___x_894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_871_, v_node_893_, v_b_875_, v___y_876_, v___y_877_);
v___y_885_ = v___x_894_;
goto v___jp_884_;
}
default: 
{
v_a_880_ = v_b_875_;
goto v___jp_879_;
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_f_871_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_b_875_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
v___jp_879_:
{
size_t v___x_881_; size_t v___x_882_; 
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_add(v_i_873_, v___x_881_);
v_i_873_ = v___x_882_;
v_b_875_ = v_a_880_;
goto _start;
}
v___jp_884_:
{
if (lean_obj_tag(v___y_885_) == 0)
{
lean_object* v_a_886_; 
v_a_886_ = lean_ctor_get(v___y_885_, 0);
if (lean_obj_tag(v_a_886_) == 0)
{
lean_dec_ref(v_f_871_);
return v___y_885_;
}
else
{
lean_object* v_a_887_; 
lean_inc_ref(v_a_886_);
lean_dec_ref(v___y_885_);
v_a_887_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v_a_886_);
v_a_880_ = v_a_887_;
goto v___jp_879_;
}
}
else
{
lean_dec_ref(v_f_871_);
return v___y_885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_f_897_, lean_object* v_as_898_, lean_object* v_i_899_, lean_object* v_stop_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
size_t v_i_boxed_905_; size_t v_stop_boxed_906_; lean_object* v_res_907_; 
v_i_boxed_905_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_stop_boxed_906_ = lean_unbox_usize(v_stop_900_);
lean_dec(v_stop_900_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_897_, v_as_898_, v_i_boxed_905_, v_stop_boxed_906_, v_b_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_as_898_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_908_, v_x_909_, v_x_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_f_915_, lean_object* v_s_916_, lean_object* v_a_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_917_);
lean_ctor_set(v___x_922_, 1, v_b_918_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
v___x_923_ = lean_apply_5(v_f_915_, v___x_922_, v_s_916_, v___y_919_, v___y_920_, lean_box(0));
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_950_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_950_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_950_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_950_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
if (lean_obj_tag(v_a_924_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_938_; 
v_a_928_ = lean_ctor_get(v_a_924_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_938_ == 0)
{
v___x_930_ = v_a_924_;
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v_a_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
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
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
v_a_939_ = lean_ctor_get(v_a_924_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_949_ == 0)
{
v___x_941_ = v_a_924_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v_a_924_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_944_);
v___x_946_ = v___x_926_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
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
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_923_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_923_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_f_959_, lean_object* v_s_960_, lean_object* v_a_961_, lean_object* v_b_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(v_f_959_, v_s_960_, v_a_961_, v_b_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(lean_object* v_map_967_, lean_object* v_init_968_, lean_object* v_f_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___f_973_; lean_object* v___x_974_; 
v___f_973_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_973_, 0, v_f_969_);
lean_inc_ref(v_map_967_);
v___x_974_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v___f_973_, v_map_967_, v_init_968_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_983_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_a_979_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_a_979_);
lean_dec(v_a_975_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_a_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_979_);
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
v_a_984_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_974_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_974_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_map_992_, lean_object* v_init_993_, lean_object* v_f_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_992_, v_init_993_, v_f_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_map_992_);
return v_res_998_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_999_; double v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_float_of_nat(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_cls_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_ref_1009_; lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1055_; 
v_ref_1009_ = lean_ctor_get(v___y_1006_, 5);
v___x_1010_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_1005_, v___y_1006_, v___y_1007_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1055_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1055_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v_traceState_1016_; lean_object* v_env_1017_; lean_object* v_nextMacroScope_1018_; lean_object* v_ngen_1019_; lean_object* v_auxDeclNGen_1020_; lean_object* v_cache_1021_; lean_object* v_messages_1022_; lean_object* v_infoState_1023_; lean_object* v_snapshotTasks_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1054_; 
v___x_1015_ = lean_st_ref_take(v___y_1007_);
v_traceState_1016_ = lean_ctor_get(v___x_1015_, 4);
v_env_1017_ = lean_ctor_get(v___x_1015_, 0);
v_nextMacroScope_1018_ = lean_ctor_get(v___x_1015_, 1);
v_ngen_1019_ = lean_ctor_get(v___x_1015_, 2);
v_auxDeclNGen_1020_ = lean_ctor_get(v___x_1015_, 3);
v_cache_1021_ = lean_ctor_get(v___x_1015_, 5);
v_messages_1022_ = lean_ctor_get(v___x_1015_, 6);
v_infoState_1023_ = lean_ctor_get(v___x_1015_, 7);
v_snapshotTasks_1024_ = lean_ctor_get(v___x_1015_, 8);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1054_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snapshotTasks_1024_);
lean_inc(v_infoState_1023_);
lean_inc(v_messages_1022_);
lean_inc(v_cache_1021_);
lean_inc(v_traceState_1016_);
lean_inc(v_auxDeclNGen_1020_);
lean_inc(v_ngen_1019_);
lean_inc(v_nextMacroScope_1018_);
lean_inc(v_env_1017_);
lean_dec(v___x_1015_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1054_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint64_t v_tid_1028_; lean_object* v_traces_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1053_; 
v_tid_1028_ = lean_ctor_get_uint64(v_traceState_1016_, sizeof(void*)*1);
v_traces_1029_ = lean_ctor_get(v_traceState_1016_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_traceState_1016_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1031_ = v_traceState_1016_;
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_traces_1029_);
lean_dec(v_traceState_1016_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; double v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0);
v___x_1035_ = 0;
v___x_1036_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1037_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1037_, 0, v_cls_1004_);
lean_ctor_set(v___x_1037_, 1, v___x_1033_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
lean_ctor_set_float(v___x_1037_, sizeof(void*)*3, v___x_1034_);
lean_ctor_set_float(v___x_1037_, sizeof(void*)*3 + 8, v___x_1034_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*3 + 16, v___x_1035_);
v___x_1038_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2));
v___x_1039_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v_a_1011_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
lean_inc(v_ref_1009_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_ref_1009_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_PersistentArray_push___redArg(v_traces_1029_, v___x_1040_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1041_);
v___x_1043_ = v___x_1031_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1041_);
lean_ctor_set_uint64(v_reuseFailAlloc_1052_, sizeof(void*)*1, v_tid_1028_);
v___x_1043_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 4, v___x_1043_);
v___x_1045_ = v___x_1026_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_env_1017_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_nextMacroScope_1018_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_ngen_1019_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_auxDeclNGen_1020_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_cache_1021_);
lean_ctor_set(v_reuseFailAlloc_1051_, 6, v_messages_1022_);
lean_ctor_set(v_reuseFailAlloc_1051_, 7, v_infoState_1023_);
lean_ctor_set(v_reuseFailAlloc_1051_, 8, v_snapshotTasks_1024_);
v___x_1045_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1046_ = lean_st_ref_set(v___y_1007_, v___x_1045_);
v___x_1047_ = lean_box(0);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1047_);
v___x_1049_ = v___x_1013_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_cls_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1056_, v_msg_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_keys_1062_, lean_object* v_i_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_array_get_size(v_keys_1062_);
v___x_1066_ = lean_nat_dec_lt(v_i_1063_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec(v_i_1063_);
return v___x_1066_;
}
else
{
lean_object* v_k_x27_1067_; uint8_t v___x_1068_; 
v_k_x27_1067_ = lean_array_fget_borrowed(v_keys_1062_, v_i_1063_);
v___x_1068_ = l_Lean_instBEqExtraModUse_beq(v_k_1064_, v_k_x27_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_i_1063_, v___x_1069_);
lean_dec(v_i_1063_);
v_i_1063_ = v___x_1070_;
goto _start;
}
else
{
lean_dec(v_i_1063_);
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_keys_1072_, lean_object* v_i_1073_, lean_object* v_k_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1072_, v_i_1073_, v_k_1074_);
lean_dec_ref(v_k_1074_);
lean_dec_ref(v_keys_1072_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_x_1077_, size_t v_x_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v_es_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v_j_1085_; lean_object* v___x_1086_; 
v_es_1080_ = lean_ctor_get(v_x_1077_, 0);
v___x_1081_ = lean_box(2);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1);
v___x_1084_ = lean_usize_land(v_x_1078_, v___x_1083_);
v_j_1085_ = lean_usize_to_nat(v___x_1084_);
v___x_1086_ = lean_array_get_borrowed(v___x_1081_, v_es_1080_, v_j_1085_);
lean_dec(v_j_1085_);
switch(lean_obj_tag(v___x_1086_))
{
case 0:
{
lean_object* v_key_1087_; uint8_t v___x_1088_; 
v_key_1087_ = lean_ctor_get(v___x_1086_, 0);
v___x_1088_ = l_Lean_instBEqExtraModUse_beq(v_x_1079_, v_key_1087_);
return v___x_1088_;
}
case 1:
{
lean_object* v_node_1089_; size_t v___x_1090_; 
v_node_1089_ = lean_ctor_get(v___x_1086_, 0);
v___x_1090_ = lean_usize_shift_right(v_x_1078_, v___x_1082_);
v_x_1077_ = v_node_1089_;
v_x_1078_ = v___x_1090_;
goto _start;
}
default: 
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
return v___x_1092_;
}
}
}
else
{
lean_object* v_ks_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_ks_1093_ = lean_ctor_get(v_x_1077_, 0);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_ks_1093_, v___x_1094_, v_x_1079_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_12210__boxed_1099_; uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_x_12210__boxed_1099_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1096_, v_x_12210__boxed_1099_, v_x_1098_);
lean_dec_ref(v_x_1098_);
lean_dec_ref(v_x_1096_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
uint64_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = l_Lean_instHashableExtraModUse_hash(v_x_1103_);
v___x_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1102_, v___x_1105_, v_x_1103_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1107_, v_x_1108_);
lean_dec_ref(v_x_1108_);
lean_dec_ref(v_x_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1));
v___x_1114_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0));
v___x_1115_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1116_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15(void){
_start:
{
lean_object* v_cls_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_cls_1135_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1136_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14));
v___x_1137_ = l_Lean_Name_append(v___x_1136_, v_cls_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_mod_1148_, uint8_t v_isMeta_1149_, lean_object* v_hint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v_env_1155_; uint8_t v_isExporting_1156_; lean_object* v___x_1157_; lean_object* v_env_1158_; lean_object* v___x_1159_; lean_object* v_entry_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___y_1165_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1154_ = lean_st_ref_get(v___y_1152_);
v_env_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc_ref(v_env_1155_);
lean_dec(v___x_1154_);
v_isExporting_1156_ = lean_ctor_get_uint8(v_env_1155_, sizeof(void*)*8);
lean_dec_ref(v_env_1155_);
v___x_1157_ = lean_st_ref_get(v___y_1152_);
v_env_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref(v_env_1158_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2);
lean_inc(v_mod_1148_);
v_entry_1160_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1160_, 0, v_mod_1148_);
lean_ctor_set_uint8(v_entry_1160_, sizeof(void*)*1, v_isExporting_1156_);
lean_ctor_set_uint8(v_entry_1160_, sizeof(void*)*1 + 1, v_isMeta_1149_);
v___x_1161_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1162_ = lean_box(1);
v___x_1163_ = lean_box(0);
v___x_1190_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1159_, v___x_1161_, v_env_1158_, v___x_1162_, v___x_1163_);
v___x_1191_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_1190_, v_entry_1160_);
lean_dec(v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v_options_1192_; uint8_t v_hasTrace_1193_; 
v_options_1192_ = lean_ctor_get(v___y_1151_, 2);
v_hasTrace_1193_ = lean_ctor_get_uint8(v_options_1192_, sizeof(void*)*1);
if (v_hasTrace_1193_ == 0)
{
lean_dec(v_hint_1150_);
lean_dec(v_mod_1148_);
v___y_1165_ = v___y_1152_;
goto v___jp_1164_;
}
else
{
lean_object* v_inheritedTraceOptions_1194_; lean_object* v_cls_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_inheritedTraceOptions_1194_ = lean_ctor_get(v___y_1151_, 13);
v_cls_1195_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1215_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15);
v___x_1216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1194_, v_options_1192_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec(v_hint_1150_);
lean_dec(v_mod_1148_);
v___y_1165_ = v___y_1152_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1217_; lean_object* v___y_1219_; 
v___x_1217_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17);
if (v_isExporting_1156_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22));
v___y_1219_ = v___x_1226_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23));
v___y_1219_ = v___x_1227_;
goto v___jp_1218_;
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc_ref(v___y_1219_);
v___x_1220_ = l_Lean_stringToMessageData(v___y_1219_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1217_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
if (v_isMeta_1149_ == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20));
v___y_1202_ = v___x_1223_;
v___y_1203_ = v___x_1224_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21));
v___y_1202_ = v___x_1223_;
v___y_1203_ = v___x_1225_;
goto v___jp_1201_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___y_1197_);
lean_ctor_set(v___x_1199_, 1, v___y_1198_);
v___x_1200_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1195_, v___x_1199_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_dec_ref(v___x_1200_);
v___y_1165_ = v___y_1152_;
goto v___jp_1164_;
}
else
{
lean_dec_ref(v_entry_1160_);
return v___x_1200_;
}
}
v___jp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
lean_inc_ref(v___y_1203_);
v___x_1204_ = l_Lean_stringToMessageData(v___y_1203_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1202_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_MessageData_ofName(v_mod_1148_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l_Lean_Name_isAnonymous(v_hint_1150_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11);
v___x_1212_ = l_Lean_MessageData_ofName(v_hint_1150_);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___y_1197_ = v___x_1209_;
v___y_1198_ = v___x_1213_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1214_; 
lean_dec(v_hint_1150_);
v___x_1214_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12);
v___y_1197_ = v___x_1209_;
v___y_1198_ = v___x_1214_;
goto v___jp_1196_;
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_entry_1160_);
lean_dec(v_hint_1150_);
lean_dec(v_mod_1148_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v_toEnvExtension_1167_; lean_object* v_env_1168_; lean_object* v_nextMacroScope_1169_; lean_object* v_ngen_1170_; lean_object* v_auxDeclNGen_1171_; lean_object* v_traceState_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1188_; 
v___x_1166_ = lean_st_ref_take(v___y_1165_);
v_toEnvExtension_1167_ = lean_ctor_get(v___x_1161_, 0);
v_env_1168_ = lean_ctor_get(v___x_1166_, 0);
v_nextMacroScope_1169_ = lean_ctor_get(v___x_1166_, 1);
v_ngen_1170_ = lean_ctor_get(v___x_1166_, 2);
v_auxDeclNGen_1171_ = lean_ctor_get(v___x_1166_, 3);
v_traceState_1172_ = lean_ctor_get(v___x_1166_, 4);
v_messages_1173_ = lean_ctor_get(v___x_1166_, 6);
v_infoState_1174_ = lean_ctor_get(v___x_1166_, 7);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1166_, 8);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1166_, 5);
lean_dec(v_unused_1189_);
v___x_1177_ = v___x_1166_;
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_traceState_1172_);
lean_inc(v_auxDeclNGen_1171_);
lean_inc(v_ngen_1170_);
lean_inc(v_nextMacroScope_1169_);
lean_inc(v_env_1168_);
lean_dec(v___x_1166_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_asyncMode_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_asyncMode_1179_ = lean_ctor_get(v_toEnvExtension_1167_, 2);
v___x_1180_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1161_, v_env_1168_, v_entry_1160_, v_asyncMode_1179_, v___x_1163_);
v___x_1181_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 5, v___x_1181_);
lean_ctor_set(v___x_1177_, 0, v___x_1180_);
v___x_1183_ = v___x_1177_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_nextMacroScope_1169_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_ngen_1170_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_auxDeclNGen_1171_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_traceState_1172_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1187_, 6, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1187_, 7, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1187_, 8, v_snapshotTasks_1175_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_st_ref_set(v___y_1165_, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_mod_1230_, lean_object* v_isMeta_1231_, lean_object* v_hint_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v_isMeta_boxed_1236_; lean_object* v_res_1237_; 
v_isMeta_boxed_1236_ = lean_unbox(v_isMeta_1231_);
v_res_1237_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_mod_1230_, v_isMeta_boxed_1236_, v_hint_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(lean_object* v___x_1238_, lean_object* v_declName_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
lean_dec(v_declName_1239_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_b_1243_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; lean_object* v_modules_1250_; lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v_toImport_1254_; lean_object* v_module_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1249_ = l_Lean_Environment_header(v___x_1238_);
v_modules_1250_ = lean_ctor_get(v___x_1249_, 3);
lean_inc_ref(v_modules_1250_);
lean_dec_ref(v___x_1249_);
v___x_1251_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1252_ = lean_array_uget_borrowed(v_as_1240_, v_i_1242_);
v___x_1253_ = lean_array_get(v___x_1251_, v_modules_1250_, v_a_1252_);
lean_dec_ref(v_modules_1250_);
v_toImport_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref(v_toImport_1254_);
lean_dec(v___x_1253_);
v_module_1255_ = lean_ctor_get(v_toImport_1254_, 0);
lean_inc(v_module_1255_);
lean_dec_ref(v_toImport_1254_);
v___x_1256_ = 0;
lean_inc(v_declName_1239_);
v___x_1257_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1255_, v___x_1256_, v_declName_1239_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; 
lean_dec_ref(v___x_1257_);
v___x_1258_ = lean_box(0);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1242_, v___x_1259_);
v_i_1242_ = v___x_1260_;
v_b_1243_ = v___x_1258_;
goto _start;
}
else
{
lean_dec(v_declName_1239_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v___x_1262_, lean_object* v_declName_1263_, lean_object* v_as_1264_, lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
size_t v_sz_boxed_1271_; size_t v_i_boxed_1272_; lean_object* v_res_1273_; 
v_sz_boxed_1271_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1272_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v___x_1262_, v_declName_1263_, v_as_1264_, v_sz_boxed_1271_, v_i_boxed_1272_, v_b_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v_as_1264_);
lean_dec_ref(v___x_1262_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(lean_object* v_a_1274_, lean_object* v_x_1275_){
_start:
{
if (lean_obj_tag(v_x_1275_) == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_box(0);
return v___x_1276_;
}
else
{
lean_object* v_key_1277_; lean_object* v_value_1278_; lean_object* v_tail_1279_; uint8_t v___x_1280_; 
v_key_1277_ = lean_ctor_get(v_x_1275_, 0);
v_value_1278_ = lean_ctor_get(v_x_1275_, 1);
v_tail_1279_ = lean_ctor_get(v_x_1275_, 2);
v___x_1280_ = lean_name_eq(v_key_1277_, v_a_1274_);
if (v___x_1280_ == 0)
{
v_x_1275_ = v_tail_1279_;
goto _start;
}
else
{
lean_object* v___x_1282_; 
lean_inc(v_value_1278_);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_value_1278_);
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_a_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1283_, v_x_1284_);
lean_dec(v_x_1284_);
lean_dec(v_a_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_buckets_1288_; lean_object* v___x_1289_; uint64_t v___y_1291_; 
v_buckets_1288_ = lean_ctor_get(v_m_1286_, 1);
v___x_1289_ = lean_array_get_size(v_buckets_1288_);
if (lean_obj_tag(v_a_1287_) == 0)
{
uint64_t v___x_1305_; 
v___x_1305_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_1291_ = v___x_1305_;
goto v___jp_1290_;
}
else
{
uint64_t v_hash_1306_; 
v_hash_1306_ = lean_ctor_get_uint64(v_a_1287_, sizeof(void*)*2);
v___y_1291_ = v_hash_1306_;
goto v___jp_1290_;
}
v___jp_1290_:
{
uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v_fold_1294_; uint64_t v___x_1295_; uint64_t v___x_1296_; uint64_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1292_ = 32ULL;
v___x_1293_ = lean_uint64_shift_right(v___y_1291_, v___x_1292_);
v_fold_1294_ = lean_uint64_xor(v___y_1291_, v___x_1293_);
v___x_1295_ = 16ULL;
v___x_1296_ = lean_uint64_shift_right(v_fold_1294_, v___x_1295_);
v___x_1297_ = lean_uint64_xor(v_fold_1294_, v___x_1296_);
v___x_1298_ = lean_uint64_to_usize(v___x_1297_);
v___x_1299_ = lean_usize_of_nat(v___x_1289_);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_sub(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_usize_land(v___x_1298_, v___x_1301_);
v___x_1303_ = lean_array_uget_borrowed(v_buckets_1288_, v___x_1302_);
v___x_1304_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1287_, v___x_1303_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg___boxed(lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_m_1307_);
return v_res_1309_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1));
v___x_1313_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0));
v___x_1314_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(lean_object* v_declName_1317_, uint8_t v_isMeta_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v_env_1326_; lean_object* v___y_1328_; lean_object* v___x_1341_; 
v___x_1322_ = lean_st_ref_get(v___y_1320_);
v_env_1326_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_ref(v_env_1326_);
lean_dec(v___x_1322_);
v___x_1341_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1326_, v_declName_1317_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref(v_env_1326_);
lean_dec(v_declName_1317_);
goto v___jp_1323_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1343_; lean_object* v_modules_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = l_Lean_Environment_header(v_env_1326_);
v_modules_1344_ = lean_ctor_get(v___x_1343_, 3);
lean_inc_ref(v_modules_1344_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_array_get_size(v_modules_1344_);
v___x_1346_ = lean_nat_dec_lt(v_val_1342_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v_modules_1344_);
lean_dec(v_val_1342_);
lean_dec_ref(v_env_1326_);
lean_dec(v_declName_1317_);
goto v___jp_1323_;
}
else
{
lean_object* v___x_1347_; lean_object* v_env_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___y_1352_; 
v___x_1347_ = lean_st_ref_get(v___y_1320_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2);
v___x_1350_ = lean_array_fget(v_modules_1344_, v_val_1342_);
lean_dec(v_val_1342_);
lean_dec_ref(v_modules_1344_);
if (v_isMeta_1318_ == 0)
{
lean_dec_ref(v_env_1348_);
v___y_1352_ = v_isMeta_1318_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1363_; 
lean_inc(v_declName_1317_);
v___x_1363_ = l_Lean_isMarkedMeta(v_env_1348_, v_declName_1317_);
if (v___x_1363_ == 0)
{
v___y_1352_ = v_isMeta_1318_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = 0;
v___y_1352_ = v___x_1364_;
goto v___jp_1351_;
}
}
v___jp_1351_:
{
lean_object* v_toImport_1353_; lean_object* v_module_1354_; lean_object* v___x_1355_; 
v_toImport_1353_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_toImport_1353_);
lean_dec(v___x_1350_);
v_module_1354_ = lean_ctor_get(v_toImport_1353_, 0);
lean_inc(v_module_1354_);
lean_dec_ref(v_toImport_1353_);
lean_inc(v_declName_1317_);
v___x_1355_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1354_, v___y_1352_, v_declName_1317_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v___x_1355_);
v___x_1356_ = l_Lean_indirectModUseExt;
v___x_1357_ = lean_box(1);
v___x_1358_ = lean_box(0);
lean_inc_ref(v_env_1326_);
v___x_1359_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1349_, v___x_1356_, v_env_1326_, v___x_1357_, v___x_1358_);
v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v___x_1359_, v_declName_1317_);
lean_dec(v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3));
v___y_1328_ = v___x_1361_;
goto v___jp_1327_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v___x_1360_);
v___y_1328_ = v_val_1362_;
goto v___jp_1327_;
}
}
else
{
lean_dec_ref(v_env_1326_);
lean_dec(v_declName_1317_);
return v___x_1355_;
}
}
}
}
v___jp_1323_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; size_t v_sz_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = lean_box(0);
v_sz_1330_ = lean_array_size(v___y_1328_);
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v_env_1326_, v_declName_1317_, v___y_1328_, v_sz_1330_, v___x_1331_, v___x_1329_, v___y_1319_, v___y_1320_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_env_1326_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v___x_1332_, 0);
lean_dec(v_unused_1340_);
v___x_1334_ = v___x_1332_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v___x_1332_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1329_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1329_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___boxed(lean_object* v_declName_1365_, lean_object* v_isMeta_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_isMeta_boxed_1370_; lean_object* v_res_1371_; 
v_isMeta_boxed_1370_ = lean_unbox(v_isMeta_1366_);
v_res_1371_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_declName_1365_, v_isMeta_boxed_1370_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(lean_object* v_ref_1372_, lean_object* v_msg_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_fileName_1377_; lean_object* v_fileMap_1378_; lean_object* v_options_1379_; lean_object* v_currRecDepth_1380_; lean_object* v_maxRecDepth_1381_; lean_object* v_ref_1382_; lean_object* v_currNamespace_1383_; lean_object* v_openDecls_1384_; lean_object* v_initHeartbeats_1385_; lean_object* v_maxHeartbeats_1386_; lean_object* v_quotContext_1387_; lean_object* v_currMacroScope_1388_; uint8_t v_diag_1389_; lean_object* v_cancelTk_x3f_1390_; uint8_t v_suppressElabErrors_1391_; lean_object* v_inheritedTraceOptions_1392_; lean_object* v_ref_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_fileName_1377_ = lean_ctor_get(v___y_1374_, 0);
v_fileMap_1378_ = lean_ctor_get(v___y_1374_, 1);
v_options_1379_ = lean_ctor_get(v___y_1374_, 2);
v_currRecDepth_1380_ = lean_ctor_get(v___y_1374_, 3);
v_maxRecDepth_1381_ = lean_ctor_get(v___y_1374_, 4);
v_ref_1382_ = lean_ctor_get(v___y_1374_, 5);
v_currNamespace_1383_ = lean_ctor_get(v___y_1374_, 6);
v_openDecls_1384_ = lean_ctor_get(v___y_1374_, 7);
v_initHeartbeats_1385_ = lean_ctor_get(v___y_1374_, 8);
v_maxHeartbeats_1386_ = lean_ctor_get(v___y_1374_, 9);
v_quotContext_1387_ = lean_ctor_get(v___y_1374_, 10);
v_currMacroScope_1388_ = lean_ctor_get(v___y_1374_, 11);
v_diag_1389_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*14);
v_cancelTk_x3f_1390_ = lean_ctor_get(v___y_1374_, 12);
v_suppressElabErrors_1391_ = lean_ctor_get_uint8(v___y_1374_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1392_ = lean_ctor_get(v___y_1374_, 13);
v_ref_1393_ = l_Lean_replaceRef(v_ref_1372_, v_ref_1382_);
lean_inc_ref(v_inheritedTraceOptions_1392_);
lean_inc(v_cancelTk_x3f_1390_);
lean_inc(v_currMacroScope_1388_);
lean_inc(v_quotContext_1387_);
lean_inc(v_maxHeartbeats_1386_);
lean_inc(v_initHeartbeats_1385_);
lean_inc(v_openDecls_1384_);
lean_inc(v_currNamespace_1383_);
lean_inc(v_maxRecDepth_1381_);
lean_inc(v_currRecDepth_1380_);
lean_inc_ref(v_options_1379_);
lean_inc_ref(v_fileMap_1378_);
lean_inc_ref(v_fileName_1377_);
v___x_1394_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1394_, 0, v_fileName_1377_);
lean_ctor_set(v___x_1394_, 1, v_fileMap_1378_);
lean_ctor_set(v___x_1394_, 2, v_options_1379_);
lean_ctor_set(v___x_1394_, 3, v_currRecDepth_1380_);
lean_ctor_set(v___x_1394_, 4, v_maxRecDepth_1381_);
lean_ctor_set(v___x_1394_, 5, v_ref_1393_);
lean_ctor_set(v___x_1394_, 6, v_currNamespace_1383_);
lean_ctor_set(v___x_1394_, 7, v_openDecls_1384_);
lean_ctor_set(v___x_1394_, 8, v_initHeartbeats_1385_);
lean_ctor_set(v___x_1394_, 9, v_maxHeartbeats_1386_);
lean_ctor_set(v___x_1394_, 10, v_quotContext_1387_);
lean_ctor_set(v___x_1394_, 11, v_currMacroScope_1388_);
lean_ctor_set(v___x_1394_, 12, v_cancelTk_x3f_1390_);
lean_ctor_set(v___x_1394_, 13, v_inheritedTraceOptions_1392_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*14, v_diag_1389_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*14 + 1, v_suppressElabErrors_1391_);
v___x_1395_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1373_, v___x_1394_, v___y_1375_);
lean_dec_ref(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_ref_1396_, lean_object* v_msg_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1396_, v_msg_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_ref_1396_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_1407_ = l_Lean_stringToMessageData(v___x_1406_);
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___x_1410_ = l_Lean_stringToMessageData(v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(lean_object* v_attrName_1411_, lean_object* v_declName_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1416_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_1417_ = l_Lean_MessageData_ofName(v_attrName_1411_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = 0;
v___x_1422_ = l_Lean_MessageData_ofConstName(v_declName_1412_, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1425_, v___y_1413_, v___y_1414_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_attrName_1427_, lean_object* v_declName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1427_, v_declName_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(uint8_t v___y_1433_, lean_object* v_as_1434_, size_t v_i_1435_, size_t v_stop_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_eq(v_i_1435_, v_stop_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; uint8_t v___y_1440_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1438_ = 1;
v___x_1444_ = lean_array_uget_borrowed(v_as_1434_, v_i_1435_);
v___x_1445_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_1446_ = lean_name_eq(v___x_1444_, v___x_1445_);
if (v___x_1446_ == 0)
{
v___y_1440_ = v___x_1437_;
goto v___jp_1439_;
}
else
{
if (v___x_1437_ == 0)
{
v___y_1440_ = v___y_1433_;
goto v___jp_1439_;
}
else
{
v___y_1440_ = v___x_1437_;
goto v___jp_1439_;
}
}
v___jp_1439_:
{
if (v___y_1440_ == 0)
{
size_t v___x_1441_; size_t v___x_1442_; 
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = lean_usize_add(v_i_1435_, v___x_1441_);
v_i_1435_ = v___x_1442_;
goto _start;
}
else
{
return v___x_1438_;
}
}
}
else
{
uint8_t v___x_1447_; 
v___x_1447_ = 0;
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1448_, lean_object* v_as_1449_, lean_object* v_i_1450_, lean_object* v_stop_1451_){
_start:
{
uint8_t v___y_12780__boxed_1452_; size_t v_i_boxed_1453_; size_t v_stop_boxed_1454_; uint8_t v_res_1455_; lean_object* v_r_1456_; 
v___y_12780__boxed_1452_ = lean_unbox(v___y_1448_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_stop_boxed_1454_ = lean_unbox_usize(v_stop_1451_);
lean_dec(v_stop_1451_);
v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_12780__boxed_1452_, v_as_1449_, v_i_boxed_1453_, v_stop_boxed_1454_);
lean_dec_ref(v_as_1449_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1462_ = l_Lean_stringToMessageData(v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1465_ = l_Lean_stringToMessageData(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1468_ = l_Lean_stringToMessageData(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v_name_1487_, lean_object* v_decl_1488_, lean_object* v_stx_1489_, uint8_t v_kind_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___f_1573_; lean_object* v___y_1575_; lean_object* v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___x_1647_; uint8_t v___x_1648_; 
lean_inc(v_decl_1488_);
v___f_1573_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed), 6, 1);
lean_closure_set(v___f_1573_, 0, v_decl_1488_);
v___x_1647_ = 0;
v___x_1648_ = l_Lean_instBEqAttributeKind_beq(v_kind_1490_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref(v___f_1573_);
lean_dec(v_stx_1489_);
lean_dec(v_decl_1488_);
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___x_1485_);
lean_dec_ref(v___x_1484_);
lean_dec(v___x_1482_);
v___x_1649_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1487_, v_kind_1490_, v___y_1491_, v___y_1492_);
return v___x_1649_;
}
else
{
goto v___jp_1642_;
}
v___jp_1494_:
{
lean_object* v___x_1497_; lean_object* v_env_1498_; lean_object* v_nextMacroScope_1499_; lean_object* v_ngen_1500_; lean_object* v_auxDeclNGen_1501_; lean_object* v_traceState_1502_; lean_object* v_messages_1503_; lean_object* v_infoState_1504_; lean_object* v_snapshotTasks_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1521_; 
v___x_1497_ = lean_st_ref_take(v___y_1496_);
v_env_1498_ = lean_ctor_get(v___x_1497_, 0);
v_nextMacroScope_1499_ = lean_ctor_get(v___x_1497_, 1);
v_ngen_1500_ = lean_ctor_get(v___x_1497_, 2);
v_auxDeclNGen_1501_ = lean_ctor_get(v___x_1497_, 3);
v_traceState_1502_ = lean_ctor_get(v___x_1497_, 4);
v_messages_1503_ = lean_ctor_get(v___x_1497_, 6);
v_infoState_1504_ = lean_ctor_get(v___x_1497_, 7);
v_snapshotTasks_1505_ = lean_ctor_get(v___x_1497_, 8);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1497_, 5);
lean_dec(v_unused_1522_);
v___x_1507_ = v___x_1497_;
v_isShared_1508_ = v_isSharedCheck_1521_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snapshotTasks_1505_);
lean_inc(v_infoState_1504_);
lean_inc(v_messages_1503_);
lean_inc(v_traceState_1502_);
lean_inc(v_auxDeclNGen_1501_);
lean_inc(v_ngen_1500_);
lean_inc(v_nextMacroScope_1499_);
lean_inc(v_env_1498_);
lean_dec(v___x_1497_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1521_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v_toEnvExtension_1510_; lean_object* v_asyncMode_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1509_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1510_ = lean_ctor_get(v___x_1509_, 0);
v_asyncMode_1511_ = lean_ctor_get(v_toEnvExtension_1510_, 2);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_decl_1488_);
lean_ctor_set(v___x_1512_, 1, v___y_1495_);
v___x_1513_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1509_, v_env_1498_, v___x_1512_, v_asyncMode_1511_, v___x_1482_);
v___x_1514_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 5, v___x_1514_);
lean_ctor_set(v___x_1507_, 0, v___x_1513_);
v___x_1516_ = v___x_1507_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_nextMacroScope_1499_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_ngen_1500_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_auxDeclNGen_1501_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_traceState_1502_);
lean_ctor_set(v_reuseFailAlloc_1520_, 5, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1520_, 6, v_messages_1503_);
lean_ctor_set(v_reuseFailAlloc_1520_, 7, v_infoState_1504_);
lean_ctor_set(v_reuseFailAlloc_1520_, 8, v_snapshotTasks_1505_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_st_ref_set(v___y_1496_, v___x_1516_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
}
v___jp_1523_:
{
lean_object* v___x_1527_; lean_object* v_env_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_st_ref_get(v___y_1526_);
v_env_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1528_);
lean_dec(v___x_1527_);
lean_inc(v___y_1524_);
v___x_1529_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1528_, v___y_1524_);
if (lean_obj_tag(v___x_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1532_ = l_Lean_MessageData_ofName(v___y_1524_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = l_Lean_MessageData_ofName(v_val_1530_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1531_);
v___x_1539_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1538_, v___y_1525_, v___y_1526_);
return v___x_1539_;
}
else
{
lean_dec(v___x_1529_);
v___y_1495_ = v___y_1524_;
v___y_1496_ = v___y_1526_;
goto v___jp_1494_;
}
}
v___jp_1540_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v___y_1542_);
v___x_1546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1547_ = l_Lean_MessageData_ofName(v_decl_1488_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
lean_inc_ref(v___y_1545_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___y_1545_);
v___x_1552_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_array_to_list(v___y_1543_);
v___x_1555_ = l_Lean_MessageData_andList(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1558_, v___y_1544_, v___y_1541_);
return v___x_1559_;
}
v___jp_1560_:
{
size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_sz_1566_ = lean_array_size(v___y_1564_);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_1566_, v___x_1567_, v___y_1564_);
v___x_1569_ = lean_array_get_size(v___x_1568_);
v___x_1570_ = lean_nat_dec_lt(v___y_1563_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1541_ = v___y_1561_;
v___y_1542_ = v___y_1562_;
v___y_1543_ = v___x_1568_;
v___y_1544_ = v___y_1565_;
v___y_1545_ = v___x_1571_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1541_ = v___y_1561_;
v___y_1542_ = v___y_1562_;
v___y_1543_ = v___x_1568_;
v___y_1544_ = v___y_1565_;
v___y_1545_ = v___x_1572_;
goto v___jp_1540_;
}
}
v___jp_1574_:
{
lean_object* v___x_1580_; lean_object* v_env_1581_; lean_object* v___x_1582_; lean_object* v_ext_1583_; lean_object* v_toEnvExtension_1584_; lean_object* v_asyncMode_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_categories_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1580_ = lean_st_ref_get(v___y_1579_);
v_env_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_env_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = l_Lean_Parser_parserExtension;
v_ext_1583_ = lean_ctor_get(v___x_1582_, 1);
v_toEnvExtension_1584_ = lean_ctor_get(v_ext_1583_, 0);
v_asyncMode_1585_ = lean_ctor_get(v_toEnvExtension_1584_, 2);
v___x_1586_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1587_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1586_, v___x_1582_, v_env_1581_, v_asyncMode_1585_);
v_categories_1588_ = lean_ctor_get(v___x_1587_, 2);
lean_inc_ref(v_categories_1588_);
lean_dec(v___x_1587_);
v___x_1589_ = lean_mk_empty_array_with_capacity(v___x_1483_);
v___x_1590_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_categories_1588_, v___x_1589_, v___f_1573_, v___y_1578_, v___y_1579_);
lean_dec_ref(v_categories_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = lean_array_get_size(v_a_1591_);
v___x_1593_ = lean_nat_dec_eq(v___x_1592_, v___x_1483_);
if (v___x_1593_ == 0)
{
if (v___y_1577_ == 0)
{
lean_dec(v_a_1591_);
v___y_1524_ = v___y_1575_;
v___y_1525_ = v___y_1578_;
v___y_1526_ = v___y_1579_;
goto v___jp_1523_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_lt(v___x_1483_, v___x_1592_);
if (v___x_1594_ == 0)
{
lean_dec(v___x_1482_);
v___y_1561_ = v___y_1579_;
v___y_1562_ = v___y_1575_;
v___y_1563_ = v___y_1576_;
v___y_1564_ = v_a_1591_;
v___y_1565_ = v___y_1578_;
goto v___jp_1560_;
}
else
{
if (v___x_1594_ == 0)
{
lean_dec(v___x_1482_);
v___y_1561_ = v___y_1579_;
v___y_1562_ = v___y_1575_;
v___y_1563_ = v___y_1576_;
v___y_1564_ = v_a_1591_;
v___y_1565_ = v___y_1578_;
goto v___jp_1560_;
}
else
{
size_t v___x_1595_; size_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = lean_usize_of_nat(v___x_1592_);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_1577_, v_a_1591_, v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec(v___x_1482_);
v___y_1561_ = v___y_1579_;
v___y_1562_ = v___y_1575_;
v___y_1563_ = v___y_1576_;
v___y_1564_ = v_a_1591_;
v___y_1565_ = v___y_1578_;
goto v___jp_1560_;
}
else
{
lean_dec(v_a_1591_);
v___y_1524_ = v___y_1575_;
v___y_1525_ = v___y_1578_;
v___y_1526_ = v___y_1579_;
goto v___jp_1523_;
}
}
}
}
}
else
{
lean_dec(v_a_1591_);
v___y_1524_ = v___y_1575_;
v___y_1525_ = v___y_1578_;
v___y_1526_ = v___y_1579_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___y_1575_);
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
v_a_1598_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1590_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1590_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1610_ = l_Lean_Name_mkStr4(v___x_1484_, v___x_1485_, v___x_1609_, v___x_1486_);
lean_inc(v_stx_1489_);
v___x_1611_ = l_Lean_Syntax_isOfKind(v_stx_1489_, v___x_1610_);
lean_dec(v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___f_1573_);
lean_dec(v_stx_1489_);
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
v___x_1612_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1613_ = l_Lean_MessageData_ofName(v_name_1487_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1616_, v___y_1607_, v___y_1608_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_name_1487_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = l_Lean_Syntax_getArg(v_stx_1489_, v___x_1618_);
lean_dec(v_stx_1489_);
v___x_1620_ = lean_box(0);
lean_inc(v___x_1619_);
v___x_1621_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1619_, v___x_1620_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc_n(v_a_1622_, 2);
lean_dec_ref(v___x_1621_);
v___x_1623_ = 0;
v___x_1624_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_a_1622_, v___x_1623_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___x_1625_; lean_object* v_env_1626_; uint8_t v___x_1627_; 
lean_dec_ref(v___x_1624_);
v___x_1625_ = lean_st_ref_get(v___y_1608_);
v_env_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_ref(v_env_1626_);
lean_dec(v___x_1625_);
v___x_1627_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1626_, v_a_1622_);
if (v___x_1627_ == 0)
{
if (v___x_1611_ == 0)
{
lean_dec(v___x_1619_);
v___y_1575_ = v_a_1622_;
v___y_1576_ = v___x_1618_;
v___y_1577_ = v___x_1611_;
v___y_1578_ = v___y_1607_;
v___y_1579_ = v___y_1608_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v___f_1573_);
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
v___x_1628_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1629_ = l_Lean_MessageData_ofName(v_a_1622_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v___x_1619_, v___x_1632_, v___y_1607_, v___y_1608_);
lean_dec(v___x_1619_);
return v___x_1633_;
}
}
else
{
lean_dec(v___x_1619_);
v___y_1575_ = v_a_1622_;
v___y_1576_ = v___x_1618_;
v___y_1577_ = v___x_1611_;
v___y_1578_ = v___y_1607_;
v___y_1579_ = v___y_1608_;
goto v___jp_1574_;
}
}
else
{
lean_dec(v_a_1622_);
lean_dec(v___x_1619_);
lean_dec_ref(v___f_1573_);
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
return v___x_1624_;
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___x_1619_);
lean_dec_ref(v___f_1573_);
lean_dec(v_decl_1488_);
lean_dec(v___x_1482_);
v_a_1634_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1621_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1621_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
v___jp_1642_:
{
lean_object* v___x_1643_; lean_object* v_env_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_st_ref_get(v___y_1492_);
v_env_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_ref(v_env_1644_);
lean_dec(v___x_1643_);
v___x_1645_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1644_, v_decl_1488_);
lean_dec_ref(v_env_1644_);
if (lean_obj_tag(v___x_1645_) == 0)
{
v___y_1607_ = v___y_1491_;
v___y_1608_ = v___y_1492_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1646_; 
lean_dec_ref(v___x_1645_);
lean_dec_ref(v___f_1573_);
lean_dec(v_stx_1489_);
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___x_1485_);
lean_dec_ref(v___x_1484_);
lean_dec(v___x_1482_);
v___x_1646_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_name_1487_, v_decl_1488_, v___y_1491_, v___y_1492_);
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, lean_object* v_name_1655_, lean_object* v_decl_1656_, lean_object* v_stx_1657_, lean_object* v_kind_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_kind_boxed_1662_; lean_object* v_res_1663_; 
v_kind_boxed_1662_ = lean_unbox(v_kind_1658_);
v_res_1663_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v___x_1650_, v___x_1651_, v___x_1652_, v___x_1653_, v___x_1654_, v_name_1655_, v_decl_1656_, v_stx_1657_, v_kind_boxed_1662_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___x_1651_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1753_ = l_Lean_registerBuiltinAttribute(v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1757_, v___y_1758_, v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_msg_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(v_00_u03b1_1762_, v_msg_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(lean_object* v_00_u03c3_1768_, lean_object* v_00_u03b2_1769_, lean_object* v_map_1770_, lean_object* v_init_1771_, lean_object* v_f_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_1770_, v_init_1771_, v_f_1772_, v___y_1773_, v___y_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03c3_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_map_1779_, lean_object* v_init_1780_, lean_object* v_f_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(v_00_u03c3_1777_, v_00_u03b2_1778_, v_map_1779_, v_init_1780_, v_f_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_map_1779_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1786_, lean_object* v_ref_1787_, lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1787_, v_msg_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_ref_1794_, lean_object* v_msg_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(v_00_u03b1_1793_, v_ref_1794_, v_msg_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_ref_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1800_, lean_object* v_attrName_1801_, lean_object* v_declName_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1801_, v_declName_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_attrName_1808_, lean_object* v_declName_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(v_00_u03b1_1807_, v_attrName_1808_, v_declName_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(lean_object* v_00_u03b1_1814_, lean_object* v_name_1815_, uint8_t v_kind_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1815_, v_kind_1816_, v___y_1817_, v___y_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_name_1822_, lean_object* v_kind_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v_kind_boxed_1827_; lean_object* v_res_1828_; 
v_kind_boxed_1827_ = lean_unbox(v_kind_1823_);
v_res_1828_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(v_00_u03b1_1821_, v_name_1822_, v_kind_boxed_1827_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1829_, lean_object* v_f_1830_, lean_object* v_init_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1830_, v_map_1829_, v_init_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1836_, lean_object* v_f_1837_, lean_object* v_init_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1836_, v_f_1837_, v_init_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1843_, lean_object* v_00_u03c3_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_map_1846_, lean_object* v_f_1847_, lean_object* v_init_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1847_, v_map_1846_, v_init_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1853_, lean_object* v_00_u03c3_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_map_1856_, lean_object* v_f_1857_, lean_object* v_init_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1853_, v_00_u03c3_1854_, v_00_u03b2_1855_, v_map_1856_, v_f_1857_, v_init_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(lean_object* v_00_u03b2_1863_, lean_object* v_m_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1864_, v_a_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___boxed(lean_object* v_00_u03b2_1867_, lean_object* v_m_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(v_00_u03b2_1867_, v_m_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_m_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1871_, lean_object* v_00_u03c3_1872_, lean_object* v_00_u03b1_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_f_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1875_, v_x_1876_, v_x_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1882_, lean_object* v_00_u03c3_1883_, lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_f_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03c3_1882_, v_00_u03c3_1883_, v_00_u03b1_1884_, v_00_u03b2_1885_, v_f_1886_, v_x_1887_, v_x_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1894_, v_x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_res_1900_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_00_u03b2_1897_, v_x_1898_, v_x_1899_);
lean_dec_ref(v_x_1899_);
lean_dec_ref(v_x_1898_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1902_, lean_object* v_a_1903_, lean_object* v_x_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(v_00_u03b2_1906_, v_a_1907_, v_x_1908_);
lean_dec(v_x_1908_);
lean_dec(v_a_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_00_u03c3_1912_, lean_object* v_00_u03c3_1913_, lean_object* v_f_1914_, lean_object* v_as_1915_, size_t v_i_1916_, size_t v_stop_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_1914_, v_as_1915_, v_i_1916_, v_stop_1917_, v_b_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_00_u03c3_1925_, lean_object* v_00_u03c3_1926_, lean_object* v_f_1927_, lean_object* v_as_1928_, lean_object* v_i_1929_, lean_object* v_stop_1930_, lean_object* v_b_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
size_t v_i_boxed_1935_; size_t v_stop_boxed_1936_; lean_object* v_res_1937_; 
v_i_boxed_1935_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_stop_boxed_1936_ = lean_unbox_usize(v_stop_1930_);
lean_dec(v_stop_1930_);
v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(v_00_u03b1_1923_, v_00_u03b2_1924_, v_00_u03c3_1925_, v_00_u03c3_1926_, v_f_1927_, v_as_1928_, v_i_boxed_1935_, v_stop_boxed_1936_, v_b_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec_ref(v_as_1928_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(lean_object* v_00_u03c3_1938_, lean_object* v_00_u03c3_1939_, lean_object* v_00_u03b1_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_f_1942_, lean_object* v_keys_1943_, lean_object* v_vals_1944_, lean_object* v_heq_1945_, lean_object* v_i_1946_, lean_object* v_acc_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_1942_, v_keys_1943_, v_vals_1944_, v_i_1946_, v_acc_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03c3_1952_, lean_object* v_00_u03c3_1953_, lean_object* v_00_u03b1_1954_, lean_object* v_00_u03b2_1955_, lean_object* v_f_1956_, lean_object* v_keys_1957_, lean_object* v_vals_1958_, lean_object* v_heq_1959_, lean_object* v_i_1960_, lean_object* v_acc_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(v_00_u03c3_1952_, v_00_u03c3_1953_, v_00_u03b1_1954_, v_00_u03b2_1955_, v_f_1956_, v_keys_1957_, v_vals_1958_, v_heq_1959_, v_i_1960_, v_acc_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec_ref(v_vals_1958_);
lean_dec_ref(v_keys_1957_);
return v_res_1965_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1966_, lean_object* v_x_1967_, size_t v_x_1968_, lean_object* v_x_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1967_, v_x_1968_, v_x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
size_t v_x_13602__boxed_1975_; uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_x_13602__boxed_1975_ = lean_unbox_usize(v_x_1973_);
lean_dec(v_x_1973_);
v_res_1976_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(v_00_u03b2_1971_, v_x_1972_, v_x_13602__boxed_1975_, v_x_1974_);
lean_dec_ref(v_x_1974_);
lean_dec_ref(v_x_1972_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(lean_object* v_00_u03b2_1978_, lean_object* v_keys_1979_, lean_object* v_vals_1980_, lean_object* v_heq_1981_, lean_object* v_i_1982_, lean_object* v_k_1983_){
_start:
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1979_, v_i_1982_, v_k_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v_00_u03b2_1985_, lean_object* v_keys_1986_, lean_object* v_vals_1987_, lean_object* v_heq_1988_, lean_object* v_i_1989_, lean_object* v_k_1990_){
_start:
{
uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_res_1991_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(v_00_u03b2_1985_, v_keys_1986_, v_vals_1987_, v_heq_1988_, v_i_1989_, v_k_1990_);
lean_dec_ref(v_k_1990_);
lean_dec_ref(v_vals_1987_);
lean_dec_ref(v_keys_1986_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v_fst_1995_; lean_object* v_snd_1996_; lean_object* v___x_1997_; 
v_fst_1995_ = lean_ctor_get(v_x_1994_, 0);
lean_inc(v_fst_1995_);
v_snd_1996_ = lean_ctor_get(v_x_1994_, 1);
lean_inc(v_snd_1996_);
lean_dec_ref(v_x_1994_);
v___x_1997_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1995_, v_snd_1996_, v_as_1993_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1998_, lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_object* v_k_2000_; lean_object* v_v_2001_; lean_object* v_l_2002_; lean_object* v_r_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_k_2000_ = lean_ctor_get(v_x_1999_, 1);
v_v_2001_ = lean_ctor_get(v_x_1999_, 2);
v_l_2002_ = lean_ctor_get(v_x_1999_, 3);
v_r_2003_ = lean_ctor_get(v_x_1999_, 4);
v___x_2004_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1998_, v_l_2002_);
lean_inc(v_v_2001_);
lean_inc(v_k_2000_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_k_2000_);
lean_ctor_set(v___x_2005_, 1, v_v_2001_);
v___x_2006_ = lean_array_push(v___x_2004_, v___x_2005_);
v_init_1998_ = v___x_2006_;
v_x_1999_ = v_r_2003_;
goto _start;
}
else
{
return v_init_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2008_, v_x_2009_);
lean_dec(v_x_2009_);
return v_res_2010_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_2011_, lean_object* v_x2_2012_){
_start:
{
lean_object* v_fst_2013_; lean_object* v_fst_2014_; uint8_t v___x_2015_; 
v_fst_2013_ = lean_ctor_get(v_x1_2011_, 0);
v_fst_2014_ = lean_ctor_get(v_x2_2012_, 0);
v___x_2015_ = l_Lean_Name_quickLt(v_fst_2013_, v_fst_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_2016_, lean_object* v_x2_2017_){
_start:
{
uint8_t v_res_2018_; lean_object* v_r_2019_; 
v_res_2018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_2016_, v_x2_2017_);
lean_dec_ref(v_x2_2017_);
lean_dec_ref(v_x1_2016_);
v_r_2019_ = lean_box(v_res_2018_);
return v_r_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_2020_, lean_object* v_pivot_2021_, lean_object* v_as_2022_, lean_object* v_i_2023_, lean_object* v_k_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_nat_dec_lt(v_k_2024_, v_hi_2020_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v_k_2024_);
v___x_2026_ = lean_array_fswap(v_as_2022_, v_i_2023_, v_hi_2020_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_i_2023_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v_fst_2029_; lean_object* v_fst_2030_; uint8_t v___x_2031_; 
v___x_2028_ = lean_array_fget_borrowed(v_as_2022_, v_k_2024_);
v_fst_2029_ = lean_ctor_get(v___x_2028_, 0);
v_fst_2030_ = lean_ctor_get(v_pivot_2021_, 0);
v___x_2031_ = l_Lean_Name_quickLt(v_fst_2029_, v_fst_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_k_2024_, v___x_2032_);
lean_dec(v_k_2024_);
v_k_2024_ = v___x_2033_;
goto _start;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2035_ = lean_array_fswap(v_as_2022_, v_i_2023_, v_k_2024_);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_add(v_i_2023_, v___x_2036_);
lean_dec(v_i_2023_);
v___x_2038_ = lean_nat_add(v_k_2024_, v___x_2036_);
lean_dec(v_k_2024_);
v_as_2022_ = v___x_2035_;
v_i_2023_ = v___x_2037_;
v_k_2024_ = v___x_2038_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_2040_, lean_object* v_pivot_2041_, lean_object* v_as_2042_, lean_object* v_i_2043_, lean_object* v_k_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2040_, v_pivot_2041_, v_as_2042_, v_i_2043_, v_k_2044_);
lean_dec_ref(v_pivot_2041_);
lean_dec(v_hi_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_2046_, lean_object* v_as_2047_, lean_object* v_lo_2048_, lean_object* v_hi_2049_){
_start:
{
lean_object* v___y_2051_; uint8_t v___x_2061_; 
v___x_2061_ = lean_nat_dec_lt(v_lo_2048_, v_hi_2049_);
if (v___x_2061_ == 0)
{
lean_dec(v_lo_2048_);
return v_as_2047_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_mid_2064_; lean_object* v___y_2066_; lean_object* v___y_2072_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2062_ = lean_nat_add(v_lo_2048_, v_hi_2049_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v_mid_2064_ = lean_nat_shiftr(v___x_2062_, v___x_2063_);
lean_dec(v___x_2062_);
v___x_2077_ = lean_array_fget_borrowed(v_as_2047_, v_mid_2064_);
v___x_2078_ = lean_array_fget_borrowed(v_as_2047_, v_lo_2048_);
v___x_2079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2077_, v___x_2078_);
if (v___x_2079_ == 0)
{
v___y_2072_ = v_as_2047_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_array_fswap(v_as_2047_, v_lo_2048_, v_mid_2064_);
v___y_2072_ = v___x_2080_;
goto v___jp_2071_;
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = lean_array_fget_borrowed(v___y_2066_, v_mid_2064_);
v___x_2068_ = lean_array_fget_borrowed(v___y_2066_, v_hi_2049_);
v___x_2069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec(v_mid_2064_);
v___y_2051_ = v___y_2066_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_array_fswap(v___y_2066_, v_mid_2064_, v_hi_2049_);
lean_dec(v_mid_2064_);
v___y_2051_ = v___x_2070_;
goto v___jp_2050_;
}
}
v___jp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_array_fget_borrowed(v___y_2072_, v_hi_2049_);
v___x_2074_ = lean_array_fget_borrowed(v___y_2072_, v_lo_2048_);
v___x_2075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
v___y_2066_ = v___y_2072_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_array_fswap(v___y_2072_, v_lo_2048_, v_hi_2049_);
v___y_2066_ = v___x_2076_;
goto v___jp_2065_;
}
}
}
v___jp_2050_:
{
lean_object* v_pivot_2052_; lean_object* v___x_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; uint8_t v___x_2056_; 
v_pivot_2052_ = lean_array_fget(v___y_2051_, v_hi_2049_);
lean_inc_n(v_lo_2048_, 2);
v___x_2053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2049_, v_pivot_2052_, v___y_2051_, v_lo_2048_, v_lo_2048_);
lean_dec(v_pivot_2052_);
v_fst_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_fst_2054_);
v_snd_2055_ = lean_ctor_get(v___x_2053_, 1);
lean_inc(v_snd_2055_);
lean_dec_ref(v___x_2053_);
v___x_2056_ = lean_nat_dec_le(v_hi_2049_, v_fst_2054_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2046_, v_snd_2055_, v_lo_2048_, v_fst_2054_);
v___x_2058_ = lean_unsigned_to_nat(1u);
v___x_2059_ = lean_nat_add(v_fst_2054_, v___x_2058_);
lean_dec(v_fst_2054_);
v_as_2047_ = v___x_2057_;
v_lo_2048_ = v___x_2059_;
goto _start;
}
else
{
lean_dec(v_fst_2054_);
lean_dec(v_lo_2048_);
return v_snd_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_2081_, lean_object* v_as_2082_, lean_object* v_lo_2083_, lean_object* v_hi_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2081_, v_as_2082_, v_lo_2083_, v_hi_2084_);
lean_dec(v_hi_2084_);
lean_dec(v_n_2081_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_2088_, lean_object* v_s_2089_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___y_2095_; lean_object* v___y_2096_; uint8_t v___x_2099_; 
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2091_, v_s_2089_);
v___x_2093_ = lean_array_get_size(v___x_2092_);
v___x_2099_ = lean_nat_dec_eq(v___x_2093_, v___x_2090_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___y_2103_; uint8_t v___x_2105_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_nat_sub(v___x_2093_, v___x_2100_);
v___x_2105_ = lean_nat_dec_le(v___x_2090_, v___x_2101_);
if (v___x_2105_ == 0)
{
lean_inc(v___x_2101_);
v___y_2103_ = v___x_2101_;
goto v___jp_2102_;
}
else
{
v___y_2103_ = v___x_2090_;
goto v___jp_2102_;
}
v___jp_2102_:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_nat_dec_le(v___y_2103_, v___x_2101_);
if (v___x_2104_ == 0)
{
lean_dec(v___x_2101_);
lean_inc(v___y_2103_);
v___y_2095_ = v___y_2103_;
v___y_2096_ = v___y_2103_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___y_2103_;
v___y_2096_ = v___x_2101_;
goto v___jp_2094_;
}
}
}
else
{
lean_object* v___x_2106_; 
lean_inc_ref_n(v___x_2092_, 2);
v___x_2106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2092_);
lean_ctor_set(v___x_2106_, 1, v___x_2092_);
lean_ctor_set(v___x_2106_, 2, v___x_2092_);
return v___x_2106_;
}
v___jp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2093_, v___x_2092_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_inc_ref_n(v___x_2097_, 2);
v___x_2098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
lean_ctor_set(v___x_2098_, 2, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_2107_, lean_object* v_s_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_2107_, v_s_2108_);
lean_dec(v_s_2108_);
lean_dec_ref(v_x_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2113_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_2112_, v_es_2110_);
v___x_2114_ = lean_array_get_size(v___x_2113_);
v___x_2115_ = lean_nat_dec_eq(v___x_2114_, v___x_2111_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2119_; uint8_t v___x_2123_; 
v___x_2116_ = lean_unsigned_to_nat(1u);
v___x_2117_ = lean_nat_sub(v___x_2114_, v___x_2116_);
v___x_2123_ = lean_nat_dec_le(v___x_2111_, v___x_2117_);
if (v___x_2123_ == 0)
{
lean_inc(v___x_2117_);
v___y_2119_ = v___x_2117_;
goto v___jp_2118_;
}
else
{
v___y_2119_ = v___x_2111_;
goto v___jp_2118_;
}
v___jp_2118_:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_le(v___y_2119_, v___x_2117_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v___x_2117_);
lean_inc(v___y_2119_);
v___x_2121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2114_, v___x_2113_, v___y_2119_, v___y_2119_);
lean_dec(v___y_2119_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_2114_, v___x_2113_, v___y_2119_, v___x_2117_);
lean_dec(v___x_2117_);
return v___x_2122_;
}
}
}
else
{
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_2124_);
lean_dec(v_es_2124_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2126_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_2131_, lean_object* v_x_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_2131_, v_x_2132_, v___y_2133_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_x_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2162_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_2165_, lean_object* v_t_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2165_, v_t_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2168_, lean_object* v_t_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_2168_, v_t_2169_);
lean_dec(v_t_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_2171_, lean_object* v_as_2172_, lean_object* v_lo_2173_, lean_object* v_hi_2174_, lean_object* v_w_2175_, lean_object* v_hlo_2176_, lean_object* v_hhi_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_n_2171_, v_as_2172_, v_lo_2173_, v_hi_2174_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_2179_, lean_object* v_as_2180_, lean_object* v_lo_2181_, lean_object* v_hi_2182_, lean_object* v_w_2183_, lean_object* v_hlo_2184_, lean_object* v_hhi_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_2179_, v_as_2180_, v_lo_2181_, v_hi_2182_, v_w_2183_, v_hlo_2184_, v_hhi_2185_);
lean_dec(v_hi_2182_);
lean_dec(v_n_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_2187_, lean_object* v_lo_2188_, lean_object* v_hi_2189_, lean_object* v_hhi_2190_, lean_object* v_pivot_2191_, lean_object* v_as_2192_, lean_object* v_i_2193_, lean_object* v_k_2194_, lean_object* v_ilo_2195_, lean_object* v_ik_2196_, lean_object* v_w_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2189_, v_pivot_2191_, v_as_2192_, v_i_2193_, v_k_2194_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_2199_, lean_object* v_lo_2200_, lean_object* v_hi_2201_, lean_object* v_hhi_2202_, lean_object* v_pivot_2203_, lean_object* v_as_2204_, lean_object* v_i_2205_, lean_object* v_k_2206_, lean_object* v_ilo_2207_, lean_object* v_ik_2208_, lean_object* v_w_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1_spec__2(v_n_2199_, v_lo_2200_, v_hi_2201_, v_hhi_2202_, v_pivot_2203_, v_as_2204_, v_i_2205_, v_k_2206_, v_ilo_2207_, v_ik_2208_, v_w_2209_);
lean_dec_ref(v_pivot_2203_);
lean_dec(v_hi_2201_);
lean_dec(v_lo_2200_);
lean_dec(v_n_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_2215_, lean_object* v___x_2216_, lean_object* v_toPure_2217_, lean_object* v___f_2218_, lean_object* v_env_2219_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2219_, v_tag_2215_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; lean_object* v_toEnvExtension_2225_; lean_object* v_asyncMode_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec_ref(v___f_2218_);
v___x_2224_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2225_ = lean_ctor_get(v___x_2224_, 0);
v_asyncMode_2226_ = lean_ctor_get(v_toEnvExtension_2225_, 2);
v___x_2227_ = lean_box(0);
v___x_2228_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2216_, v___x_2224_, v_env_2219_, v_asyncMode_2226_, v___x_2227_);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2228_, v_tag_2215_);
lean_dec(v_tag_2215_);
lean_dec(v___x_2228_);
v___x_2230_ = lean_apply_2(v_toPure_2217_, lean_box(0), v___x_2229_);
return v___x_2230_;
}
else
{
lean_object* v_val_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_val_2231_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2231_);
lean_dec_ref(v___x_2223_);
v___x_2232_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2233_ = 0;
v___x_2234_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2216_, v___x_2232_, v_env_2219_, v_val_2231_, v___x_2233_);
lean_dec(v_val_2231_);
lean_dec_ref(v_env_2219_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_array_get_size(v___x_2234_);
v___x_2237_ = lean_nat_dec_lt(v___x_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___f_2218_);
lean_dec(v_tag_2215_);
goto v___jp_2220_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_sub(v___x_2236_, v___x_2238_);
v___x_2240_ = lean_nat_dec_le(v___x_2235_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_dec(v___x_2239_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___f_2218_);
lean_dec(v_tag_2215_);
goto v___jp_2220_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2241_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_tag_2215_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_2244_ = l_Array_binSearchAux___redArg(v___f_2218_, v___x_2243_, v___x_2234_, v___x_2242_, v___x_2235_, v___x_2239_);
lean_dec_ref(v___x_2234_);
if (lean_obj_tag(v___x_2244_) == 0)
{
goto v___jp_2220_;
}
else
{
lean_object* v_val_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2254_; 
v_val_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_val_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_snd_2249_; lean_object* v___x_2251_; 
v_snd_2249_ = lean_ctor_get(v_val_2245_, 1);
lean_inc(v_snd_2249_);
lean_dec(v_val_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_snd_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_snd_2249_);
v___x_2251_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_apply_2(v_toPure_2217_, lean_box(0), v___x_2251_);
return v___x_2252_;
}
}
}
}
}
}
v___jp_2220_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_apply_2(v_toPure_2217_, lean_box(0), v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_tag_2258_){
_start:
{
lean_object* v_toApplicative_2259_; lean_object* v_toBind_2260_; lean_object* v_getEnv_2261_; lean_object* v_toPure_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; 
v_toApplicative_2259_ = lean_ctor_get(v_inst_2256_, 0);
lean_inc_ref(v_toApplicative_2259_);
v_toBind_2260_ = lean_ctor_get(v_inst_2256_, 1);
lean_inc(v_toBind_2260_);
lean_dec_ref(v_inst_2256_);
v_getEnv_2261_ = lean_ctor_get(v_inst_2257_, 0);
lean_inc(v_getEnv_2261_);
lean_dec_ref(v_inst_2257_);
v_toPure_2262_ = lean_ctor_get(v_toApplicative_2259_, 1);
lean_inc(v_toPure_2262_);
lean_dec_ref(v_toApplicative_2259_);
v___f_2263_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___closed__0));
v___x_2264_ = lean_box(1);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2265_, 0, v_tag_2258_);
lean_closure_set(v___f_2265_, 1, v___x_2264_);
lean_closure_set(v___f_2265_, 2, v_toPure_2262_);
lean_closure_set(v___f_2265_, 3, v___f_2263_);
v___x_2266_ = lean_apply_4(v_toBind_2260_, lean_box(0), lean_box(0), v_getEnv_2261_, v___f_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_tag_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_2268_, v_inst_2269_, v_tag_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_2272_, lean_object* v_k_2273_, lean_object* v_x_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_array_push(v_l_2272_, v_k_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_2276_, lean_object* v_x2_2277_){
_start:
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2278_ = 1;
v___x_2279_ = l_Lean_Name_toString(v_x1_2276_, v___x_2278_);
v___x_2280_ = l_Lean_Name_toString(v_x2_2277_, v___x_2278_);
v___x_2281_ = lean_string_dec_lt(v___x_2279_, v___x_2280_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_2282_, lean_object* v_x2_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_2282_, v_x2_2283_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_, lean_object* v_c_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = l_Lean_NameSet_insert(v_c_2289_, v_a_2287_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
v___x_2292_ = lean_apply_2(v_toPure_2286_, lean_box(0), v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_2293_, lean_object* v_a_2294_, lean_object* v_b_2295_, lean_object* v_c_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_2293_, v_a_2294_, v_b_2295_, v_c_2296_);
lean_dec_ref(v_b_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_2298_, lean_object* v_a_2299_, lean_object* v_x_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_fst_2302_; lean_object* v_found_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_fst_2302_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_fst_2302_);
lean_dec_ref(v_a_2299_);
v_found_2303_ = l_Lean_NameSet_insert(v___y_2301_, v_fst_2302_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_found_2303_);
v___x_2305_ = lean_apply_2(v_toPure_2298_, lean_box(0), v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_2306_, lean_object* v___f_2307_, lean_object* v_toBind_2308_, lean_object* v___f_2309_, lean_object* v_a_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_){
_start:
{
size_t v_sz_2313_; size_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_sz_2313_ = lean_array_size(v_a_2310_);
v___x_2314_ = ((size_t)0ULL);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2306_, v_a_2310_, v___f_2307_, v_sz_2313_, v___x_2314_, v___y_2312_);
v___x_2316_ = lean_apply_4(v_toBind_2308_, lean_box(0), lean_box(0), v___x_2315_, v___f_2309_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_2317_, lean_object* v___f_2318_, lean_object* v___f_2319_, lean_object* v_____s_2320_){
_start:
{
lean_object* v___y_2322_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2338_; 
if (lean_obj_tag(v_____s_2320_) == 0)
{
lean_object* v_size_2347_; 
v_size_2347_ = lean_ctor_get(v_____s_2320_, 0);
lean_inc(v_size_2347_);
v___y_2338_ = v_size_2347_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___y_2338_ = v___x_2348_;
goto v___jp_2337_;
}
v___jp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_array_to_list(v___y_2322_);
v___x_2324_ = lean_apply_2(v_toPure_2317_, lean_box(0), v___x_2323_);
return v___x_2324_;
}
v___jp_2325_:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2318_, v___y_2328_, v___y_2326_, v___y_2327_, v___y_2329_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2329_);
lean_dec(v___y_2328_);
v___y_2322_ = v___x_2330_;
goto v___jp_2321_;
}
v___jp_2331_:
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_nat_dec_le(v___y_2335_, v___y_2334_);
if (v___x_2336_ == 0)
{
lean_dec(v___y_2334_);
lean_inc(v___y_2335_);
v___y_2326_ = v___y_2332_;
v___y_2327_ = v___y_2335_;
v___y_2328_ = v___y_2333_;
v___y_2329_ = v___y_2335_;
goto v___jp_2325_;
}
else
{
v___y_2326_ = v___y_2332_;
v___y_2327_ = v___y_2335_;
v___y_2328_ = v___y_2333_;
v___y_2329_ = v___y_2334_;
goto v___jp_2325_;
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2339_ = lean_mk_empty_array_with_capacity(v___y_2338_);
lean_dec(v___y_2338_);
v___x_2340_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2319_, v___x_2339_, v_____s_2320_);
v___x_2341_ = lean_array_get_size(v___x_2340_);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_nat_dec_eq(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_nat_sub(v___x_2341_, v___x_2344_);
v___x_2346_ = lean_nat_dec_le(v___x_2342_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_inc(v___x_2345_);
v___y_2332_ = v___x_2340_;
v___y_2333_ = v___x_2341_;
v___y_2334_ = v___x_2345_;
v___y_2335_ = v___x_2345_;
goto v___jp_2331_;
}
else
{
v___y_2332_ = v___x_2340_;
v___y_2333_ = v___x_2341_;
v___y_2334_ = v___x_2345_;
v___y_2335_ = v___x_2342_;
goto v___jp_2331_;
}
}
else
{
lean_dec_ref(v___f_2318_);
v___y_2322_ = v___x_2340_;
goto v___jp_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2349_, lean_object* v_toEnvExtension_2350_, lean_object* v_env_2351_, lean_object* v_asyncMode_2352_, lean_object* v___x_2353_, lean_object* v_inst_2354_, lean_object* v___f_2355_, lean_object* v_toBind_2356_, lean_object* v___f_2357_, lean_object* v_____s_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v_importedEntries_2360_; size_t v_sz_2361_; size_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2359_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2349_, v_toEnvExtension_2350_, v_env_2351_, v_asyncMode_2352_, v___x_2353_);
v_importedEntries_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_importedEntries_2360_);
lean_dec(v___x_2359_);
v_sz_2361_ = lean_array_size(v_importedEntries_2360_);
v___x_2362_ = ((size_t)0ULL);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2354_, v_importedEntries_2360_, v___f_2355_, v_sz_2361_, v___x_2362_, v_____s_2358_);
v___x_2364_ = lean_apply_4(v_toBind_2356_, lean_box(0), lean_box(0), v___x_2363_, v___f_2357_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2365_, lean_object* v_toEnvExtension_2366_, lean_object* v_env_2367_, lean_object* v_asyncMode_2368_, lean_object* v___x_2369_, lean_object* v_inst_2370_, lean_object* v___f_2371_, lean_object* v_toBind_2372_, lean_object* v___f_2373_, lean_object* v_____s_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2365_, v_toEnvExtension_2366_, v_env_2367_, v_asyncMode_2368_, v___x_2369_, v_inst_2370_, v___f_2371_, v_toBind_2372_, v___f_2373_, v_____s_2374_);
lean_dec(v_asyncMode_2368_);
lean_dec_ref(v_toEnvExtension_2366_);
lean_dec_ref(v___x_2365_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2376_, lean_object* v_inst_2377_, lean_object* v___f_2378_, lean_object* v_toBind_2379_, lean_object* v___f_2380_, lean_object* v___x_2381_, lean_object* v___f_2382_, lean_object* v___f_2383_, lean_object* v_env_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v_toEnvExtension_2386_; lean_object* v_asyncMode_2387_; lean_object* v_found_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2385_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2386_ = lean_ctor_get(v___x_2385_, 0);
v_asyncMode_2387_ = lean_ctor_get(v_toEnvExtension_2386_, 2);
v_found_2388_ = l_Lean_NameSet_empty;
v___x_2389_ = lean_box(0);
lean_inc_n(v_toBind_2379_, 2);
lean_inc_ref(v_inst_2377_);
lean_inc(v_asyncMode_2387_);
lean_inc_ref(v_env_2384_);
lean_inc_ref(v_toEnvExtension_2386_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2390_, 0, v___x_2376_);
lean_closure_set(v___f_2390_, 1, v_toEnvExtension_2386_);
lean_closure_set(v___f_2390_, 2, v_env_2384_);
lean_closure_set(v___f_2390_, 3, v_asyncMode_2387_);
lean_closure_set(v___f_2390_, 4, v___x_2389_);
lean_closure_set(v___f_2390_, 5, v_inst_2377_);
lean_closure_set(v___f_2390_, 6, v___f_2378_);
lean_closure_set(v___f_2390_, 7, v_toBind_2379_);
lean_closure_set(v___f_2390_, 8, v___f_2380_);
v___x_2391_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2381_, v___x_2385_, v_env_2384_, v_asyncMode_2387_, v___x_2389_);
v___x_2392_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2377_, v___f_2382_, v_found_2388_, v___x_2391_);
v___x_2393_ = lean_apply_4(v_toBind_2379_, lean_box(0), lean_box(0), v___x_2392_, v___f_2383_);
v___x_2394_ = lean_apply_4(v_toBind_2379_, lean_box(0), lean_box(0), v___x_2393_, v___f_2390_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_box(1);
v___x_2398_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2399_, lean_object* v_inst_2400_){
_start:
{
lean_object* v_toApplicative_2401_; lean_object* v_toBind_2402_; lean_object* v_getEnv_2403_; lean_object* v_toPure_2404_; lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___f_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; 
v_toApplicative_2401_ = lean_ctor_get(v_inst_2399_, 0);
v_toBind_2402_ = lean_ctor_get(v_inst_2399_, 1);
lean_inc_n(v_toBind_2402_, 3);
v_getEnv_2403_ = lean_ctor_get(v_inst_2400_, 0);
lean_inc(v_getEnv_2403_);
lean_dec_ref(v_inst_2400_);
v_toPure_2404_ = lean_ctor_get(v_toApplicative_2401_, 1);
v___f_2405_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2406_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2407_ = lean_box(1);
v___x_2408_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2404_, 5);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2409_, 0, v_toPure_2404_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2410_, 0, v_toPure_2404_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2411_, 0, v_toPure_2404_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2412_, 0, v_toPure_2404_);
lean_inc_ref(v_inst_2399_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2413_, 0, v_inst_2399_);
lean_closure_set(v___f_2413_, 1, v___f_2411_);
lean_closure_set(v___f_2413_, 2, v_toBind_2402_);
lean_closure_set(v___f_2413_, 3, v___f_2412_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2414_, 0, v_toPure_2404_);
lean_closure_set(v___f_2414_, 1, v___f_2406_);
lean_closure_set(v___f_2414_, 2, v___f_2405_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2415_, 0, v___x_2408_);
lean_closure_set(v___f_2415_, 1, v_inst_2399_);
lean_closure_set(v___f_2415_, 2, v___f_2413_);
lean_closure_set(v___f_2415_, 3, v_toBind_2402_);
lean_closure_set(v___f_2415_, 4, v___f_2414_);
lean_closure_set(v___f_2415_, 5, v___x_2407_);
lean_closure_set(v___f_2415_, 6, v___f_2410_);
lean_closure_set(v___f_2415_, 7, v___f_2409_);
v___x_2416_ = lean_apply_4(v_toBind_2402_, lean_box(0), lean_box(0), v_getEnv_2403_, v___f_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2418_, v_inst_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2421_, lean_object* v_k_2422_, lean_object* v_v_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_k_2422_);
lean_ctor_set(v___x_2424_, 1, v_v_2423_);
v___x_2425_ = lean_array_push(v_arr_2421_, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2426_, lean_object* v_x2_2427_){
_start:
{
lean_object* v_fst_2428_; lean_object* v_fst_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_fst_2428_ = lean_ctor_get(v_x1_2426_, 0);
lean_inc(v_fst_2428_);
lean_dec_ref(v_x1_2426_);
v_fst_2429_ = lean_ctor_get(v_x2_2427_, 0);
lean_inc(v_fst_2429_);
lean_dec_ref(v_x2_2427_);
v___x_2430_ = 1;
v___x_2431_ = l_Lean_Name_toString(v_fst_2428_, v___x_2430_);
v___x_2432_ = l_Lean_Name_toString(v_fst_2429_, v___x_2430_);
v___x_2433_ = lean_string_dec_lt(v___x_2431_, v___x_2432_);
lean_dec_ref(v___x_2432_);
lean_dec_ref(v___x_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2434_, lean_object* v_x2_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2434_, v_x2_2435_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_, lean_object* v_c_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2439_, v_b_2440_, v_c_2441_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
v___x_2444_ = lean_apply_2(v_toPure_2438_, lean_box(0), v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2445_, lean_object* v_a_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v_found_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_fst_2449_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v_a_2446_, 1);
lean_inc(v_snd_2450_);
lean_dec_ref(v_a_2446_);
v_found_2451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2449_, v_snd_2450_, v___y_2448_);
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_found_2451_);
v___x_2453_ = lean_apply_2(v_toPure_2445_, lean_box(0), v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2454_, lean_object* v___f_2455_, lean_object* v___f_2456_, lean_object* v_____s_2457_){
_start:
{
lean_object* v___y_2459_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_arr_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; uint8_t v___x_2470_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2464_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2455_, v___x_2463_, v_____s_2457_);
v___x_2465_ = lean_array_get_size(v_arr_2464_);
v___x_2470_ = lean_nat_dec_eq(v___x_2465_, v___x_2462_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___y_2474_; uint8_t v___x_2476_; 
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = lean_nat_sub(v___x_2465_, v___x_2471_);
v___x_2476_ = lean_nat_dec_le(v___x_2462_, v___x_2472_);
if (v___x_2476_ == 0)
{
lean_inc(v___x_2472_);
v___y_2474_ = v___x_2472_;
goto v___jp_2473_;
}
else
{
v___y_2474_ = v___x_2462_;
goto v___jp_2473_;
}
v___jp_2473_:
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_nat_dec_le(v___y_2474_, v___x_2472_);
if (v___x_2475_ == 0)
{
lean_dec(v___x_2472_);
lean_inc(v___y_2474_);
v___y_2467_ = v___y_2474_;
v___y_2468_ = v___y_2474_;
goto v___jp_2466_;
}
else
{
v___y_2467_ = v___y_2474_;
v___y_2468_ = v___x_2472_;
goto v___jp_2466_;
}
}
}
else
{
lean_dec_ref(v___f_2456_);
v___y_2459_ = v_arr_2464_;
goto v___jp_2458_;
}
v___jp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_array_to_list(v___y_2459_);
v___x_2461_ = lean_apply_2(v_toPure_2454_, lean_box(0), v___x_2460_);
return v___x_2461_;
}
v___jp_2466_:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2456_, v___x_2465_, v_arr_2464_, v___y_2467_, v___y_2468_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2468_);
v___y_2459_ = v___x_2469_;
goto v___jp_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2477_, lean_object* v_inst_2478_, lean_object* v___f_2479_, lean_object* v_toBind_2480_, lean_object* v___f_2481_, lean_object* v___x_2482_, lean_object* v___f_2483_, lean_object* v___f_2484_, lean_object* v_env_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v_toEnvExtension_2487_; lean_object* v_asyncMode_2488_; lean_object* v_found_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2486_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2487_ = lean_ctor_get(v___x_2486_, 0);
v_asyncMode_2488_ = lean_ctor_get(v_toEnvExtension_2487_, 2);
v_found_2489_ = lean_box(1);
v___x_2490_ = lean_box(0);
lean_inc_n(v_toBind_2480_, 2);
lean_inc_ref(v_inst_2478_);
lean_inc(v_asyncMode_2488_);
lean_inc_ref(v_env_2485_);
lean_inc_ref(v_toEnvExtension_2487_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2491_, 0, v___x_2477_);
lean_closure_set(v___f_2491_, 1, v_toEnvExtension_2487_);
lean_closure_set(v___f_2491_, 2, v_env_2485_);
lean_closure_set(v___f_2491_, 3, v_asyncMode_2488_);
lean_closure_set(v___f_2491_, 4, v___x_2490_);
lean_closure_set(v___f_2491_, 5, v_inst_2478_);
lean_closure_set(v___f_2491_, 6, v___f_2479_);
lean_closure_set(v___f_2491_, 7, v_toBind_2480_);
lean_closure_set(v___f_2491_, 8, v___f_2481_);
v___x_2492_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2482_, v___x_2486_, v_env_2485_, v_asyncMode_2488_, v___x_2490_);
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2478_, v___f_2483_, v_found_2489_, v___x_2492_);
v___x_2494_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2493_, v___f_2484_);
v___x_2495_ = lean_apply_4(v_toBind_2480_, lean_box(0), lean_box(0), v___x_2494_, v___f_2491_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2498_, lean_object* v_inst_2499_){
_start:
{
lean_object* v_toApplicative_2500_; lean_object* v_toBind_2501_; lean_object* v_getEnv_2502_; lean_object* v_toPure_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; 
v_toApplicative_2500_ = lean_ctor_get(v_inst_2498_, 0);
v_toBind_2501_ = lean_ctor_get(v_inst_2498_, 1);
lean_inc_n(v_toBind_2501_, 3);
v_getEnv_2502_ = lean_ctor_get(v_inst_2499_, 0);
lean_inc(v_getEnv_2502_);
lean_dec_ref(v_inst_2499_);
v_toPure_2503_ = lean_ctor_get(v_toApplicative_2500_, 1);
v___f_2504_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2505_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2506_ = lean_box(1);
v___x_2507_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2503_, 5);
v___f_2508_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2508_, 0, v_toPure_2503_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2509_, 0, v_toPure_2503_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2510_, 0, v_toPure_2503_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2511_, 0, v_toPure_2503_);
lean_inc_ref(v_inst_2498_);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2512_, 0, v_inst_2498_);
lean_closure_set(v___f_2512_, 1, v___f_2510_);
lean_closure_set(v___f_2512_, 2, v_toBind_2501_);
lean_closure_set(v___f_2512_, 3, v___f_2511_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2513_, 0, v_toPure_2503_);
lean_closure_set(v___f_2513_, 1, v___f_2504_);
lean_closure_set(v___f_2513_, 2, v___f_2505_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2514_, 0, v___x_2507_);
lean_closure_set(v___f_2514_, 1, v_inst_2498_);
lean_closure_set(v___f_2514_, 2, v___f_2512_);
lean_closure_set(v___f_2514_, 3, v_toBind_2501_);
lean_closure_set(v___f_2514_, 4, v___f_2513_);
lean_closure_set(v___f_2514_, 5, v___x_2506_);
lean_closure_set(v___f_2514_, 6, v___f_2509_);
lean_closure_set(v___f_2514_, 7, v___f_2508_);
v___x_2515_ = lean_apply_4(v_toBind_2501_, lean_box(0), lean_box(0), v_getEnv_2502_, v___f_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2517_, v_inst_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2520_, lean_object* v_init_2521_, lean_object* v_x_2522_){
_start:
{
if (lean_obj_tag(v_x_2522_) == 0)
{
lean_object* v_k_2523_; lean_object* v_l_2524_; lean_object* v_r_2525_; lean_object* v___x_2526_; lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_k_2523_ = lean_ctor_get(v_x_2522_, 1);
v_l_2524_ = lean_ctor_get(v_x_2522_, 3);
v_r_2525_ = lean_ctor_get(v_x_2522_, 4);
lean_inc_n(v_a_2520_, 2);
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2520_, v_init_2521_, v_l_2524_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref(v___x_2526_);
lean_inc(v_k_2523_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2520_);
lean_ctor_set(v___x_2528_, 1, v_k_2523_);
v___x_2529_ = lean_array_push(v_a_2527_, v___x_2528_);
v_init_2521_ = v___x_2529_;
v_x_2522_ = v_r_2525_;
goto _start;
}
else
{
lean_object* v___x_2531_; 
lean_dec(v_a_2520_);
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_init_2521_);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2532_, lean_object* v_init_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2532_, v_init_2533_, v_x_2534_);
lean_dec(v_x_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2536_, lean_object* v_x_2537_){
_start:
{
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_object* v_k_2538_; lean_object* v_v_2539_; lean_object* v_l_2540_; lean_object* v_r_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; 
v_k_2538_ = lean_ctor_get(v_x_2537_, 1);
lean_inc(v_k_2538_);
v_v_2539_ = lean_ctor_get(v_x_2537_, 2);
lean_inc(v_v_2539_);
v_l_2540_ = lean_ctor_get(v_x_2537_, 3);
lean_inc(v_l_2540_);
v_r_2541_ = lean_ctor_get(v_x_2537_, 4);
lean_inc(v_r_2541_);
lean_dec_ref(v_x_2537_);
v___x_2542_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2536_, v_l_2540_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2538_, v_a_2543_, v_v_2539_);
lean_dec(v_v_2539_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v_init_2536_ = v_a_2545_;
v_x_2537_ = v_r_2541_;
goto _start;
}
else
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_init_2536_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2548_){
_start:
{
lean_object* v_exported_2549_; lean_object* v___x_2550_; lean_object* v_a_2551_; 
v_exported_2549_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2550_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2549_, v_tags_2548_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
return v_a_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2552_, lean_object* v_s_2553_){
_start:
{
lean_object* v_exported_2554_; lean_object* v___x_2555_; lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_exported_2554_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2554_, v_s_2553_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_n(v_a_2556_, 3);
lean_dec_ref(v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2556_);
lean_ctor_set(v___x_2557_, 1, v_a_2556_);
lean_ctor_set(v___x_2557_, 2, v_a_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2558_, lean_object* v_s_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2558_, v_s_2559_);
lean_dec_ref(v_x_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2561_, lean_object* v_k_2562_, lean_object* v_fallback_2563_){
_start:
{
if (lean_obj_tag(v_t_2561_) == 0)
{
lean_object* v_k_2564_; lean_object* v_v_2565_; lean_object* v_l_2566_; lean_object* v_r_2567_; uint8_t v___x_2568_; 
v_k_2564_ = lean_ctor_get(v_t_2561_, 1);
v_v_2565_ = lean_ctor_get(v_t_2561_, 2);
v_l_2566_ = lean_ctor_get(v_t_2561_, 3);
v_r_2567_ = lean_ctor_get(v_t_2561_, 4);
v___x_2568_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2562_, v_k_2564_);
switch(v___x_2568_)
{
case 0:
{
v_t_2561_ = v_l_2566_;
goto _start;
}
case 1:
{
lean_inc(v_v_2565_);
return v_v_2565_;
}
default: 
{
v_t_2561_ = v_r_2567_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2563_);
return v_fallback_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2571_, lean_object* v_k_2572_, lean_object* v_fallback_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2571_, v_k_2572_, v_fallback_2573_);
lean_dec(v_fallback_2573_);
lean_dec(v_k_2572_);
lean_dec(v_t_2571_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2575_, lean_object* v_x_2576_){
_start:
{
lean_object* v_fst_2577_; lean_object* v_snd_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_fst_2577_ = lean_ctor_get(v_x_2576_, 0);
lean_inc(v_fst_2577_);
v_snd_2578_ = lean_ctor_get(v_x_2576_, 1);
lean_inc(v_snd_2578_);
lean_dec_ref(v_x_2576_);
v___x_2579_ = l_Lean_NameSet_empty;
v___x_2580_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2575_, v_fst_2577_, v___x_2579_);
v___x_2581_ = l_Lean_NameSet_insert(v___x_2580_, v_snd_2578_);
v___x_2582_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2577_, v___x_2581_, v_tags_2575_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2607_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2610_, lean_object* v_t_2611_, lean_object* v_k_2612_, lean_object* v_fallback_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2611_, v_k_2612_, v_fallback_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2615_, lean_object* v_t_2616_, lean_object* v_k_2617_, lean_object* v_fallback_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2615_, v_t_2616_, v_k_2617_, v_fallback_2618_);
lean_dec(v_fallback_2618_);
lean_dec(v_k_2617_);
lean_dec(v_t_2616_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v_name_2620_, lean_object* v_decl_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2625_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2626_ = l_Lean_MessageData_ofName(v_name_2620_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_2629_, v___y_2622_, v___y_2623_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_name_2631_, lean_object* v_decl_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v_name_2631_, v_decl_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v_decl_2632_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
if (lean_obj_tag(v_a_2637_) == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = l_List_reverse___redArg(v_a_2638_);
return v___x_2639_;
}
else
{
lean_object* v_head_2640_; lean_object* v_tail_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2653_; 
v_head_2640_ = lean_ctor_get(v_a_2637_, 0);
v_tail_2641_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2643_ = v_a_2637_;
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_tail_2641_);
lean_inc(v_head_2640_);
lean_dec(v_a_2637_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2653_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2646_ = l_Lean_MessageData_ofName(v_head_2640_);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___x_2645_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 1, v_a_2638_);
lean_ctor_set(v___x_2643_, 0, v___x_2648_);
v___x_2650_ = v___x_2643_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_a_2638_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
v_a_2637_ = v_tail_2641_;
v_a_2638_ = v___x_2650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2654_, lean_object* v_k_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v_m_2660_; lean_object* v_a_2661_; uint8_t v___x_2662_; 
v___x_2658_ = lean_nat_add(v_x_2656_, v_x_2657_);
v___x_2659_ = lean_unsigned_to_nat(1u);
v_m_2660_ = lean_nat_shiftr(v___x_2658_, v___x_2659_);
lean_dec(v___x_2658_);
v_a_2661_ = lean_array_fget_borrowed(v_as_2654_, v_m_2660_);
v___x_2662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2661_, v_k_2655_);
if (v___x_2662_ == 0)
{
uint8_t v___x_2663_; 
lean_dec(v_x_2657_);
v___x_2663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2655_, v_a_2661_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec(v_m_2660_);
lean_dec(v_x_2656_);
lean_inc(v_a_2661_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_a_2661_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_nat_dec_eq(v_m_2660_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_nat_sub(v_m_2660_, v___x_2659_);
lean_dec(v_m_2660_);
v___x_2668_ = lean_nat_dec_lt(v___x_2667_, v_x_2656_);
if (v___x_2668_ == 0)
{
v_x_2657_ = v___x_2667_;
goto _start;
}
else
{
lean_object* v___x_2670_; 
lean_dec(v___x_2667_);
lean_dec(v_x_2656_);
v___x_2670_ = lean_box(0);
return v___x_2670_;
}
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_m_2660_);
lean_dec(v_x_2656_);
v___x_2671_ = lean_box(0);
return v___x_2671_;
}
}
}
else
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
lean_dec(v_x_2656_);
v___x_2672_ = lean_nat_add(v_m_2660_, v___x_2659_);
lean_dec(v_m_2660_);
v___x_2673_ = lean_nat_dec_le(v___x_2672_, v_x_2657_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec(v___x_2672_);
lean_dec(v_x_2657_);
v___x_2674_ = lean_box(0);
return v___x_2674_;
}
else
{
v_x_2656_ = v___x_2672_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2676_, lean_object* v_k_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2676_, v_k_2677_, v_x_2678_, v_x_2679_);
lean_dec_ref(v_k_2677_);
lean_dec_ref(v_as_2676_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; lean_object* v_env_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2684_ = lean_st_ref_get(v___y_2682_);
v_env_2688_ = lean_ctor_get(v___x_2684_, 0);
lean_inc_ref(v_env_2688_);
lean_dec(v___x_2684_);
v___x_2689_ = lean_box(1);
v___x_2690_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2688_, v_tag_2681_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2691_; lean_object* v_toEnvExtension_2692_; lean_object* v_asyncMode_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2691_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2692_ = lean_ctor_get(v___x_2691_, 0);
v_asyncMode_2693_ = lean_ctor_get(v_toEnvExtension_2692_, 2);
v___x_2694_ = lean_box(0);
v___x_2695_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2689_, v___x_2691_, v_env_2688_, v_asyncMode_2693_, v___x_2694_);
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2695_, v_tag_2681_);
lean_dec(v_tag_2681_);
lean_dec(v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
else
{
lean_object* v_val_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2726_; 
v_val_2698_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2700_ = v___x_2690_;
v_isShared_2701_ = v_isSharedCheck_2726_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_val_2698_);
lean_dec(v___x_2690_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2726_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2702_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2703_ = 0;
v___x_2704_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2689_, v___x_2702_, v_env_2688_, v_val_2698_, v___x_2703_);
lean_dec(v_val_2698_);
lean_dec_ref(v_env_2688_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v___x_2704_);
v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_dec_ref(v___x_2704_);
lean_del_object(v___x_2700_);
lean_dec(v_tag_2681_);
goto v___jp_2685_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_sub(v___x_2706_, v___x_2708_);
v___x_2710_ = lean_nat_dec_le(v___x_2705_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_dec(v___x_2709_);
lean_dec_ref(v___x_2704_);
lean_del_object(v___x_2700_);
lean_dec(v_tag_2681_);
goto v___jp_2685_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_tag_2681_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2704_, v___x_2712_, v___x_2705_, v___x_2709_);
lean_dec_ref(v___x_2712_);
lean_dec_ref(v___x_2704_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_del_object(v___x_2700_);
goto v___jp_2685_;
}
else
{
lean_object* v_val_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2725_; 
v_val_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_val_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_snd_2718_; lean_object* v___x_2720_; 
v_snd_2718_ = lean_ctor_get(v_val_2714_, 1);
lean_inc(v_snd_2718_);
lean_dec(v_val_2714_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v_snd_2718_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_snd_2718_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2720_);
v___x_2722_ = v___x_2700_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
}
}
v___jp_2685_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2727_, v___y_2728_);
lean_dec(v___y_2728_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2731_, size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_b_2734_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_usize_dec_lt(v_i_2733_, v_sz_2732_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_b_2734_);
return v___x_2737_;
}
else
{
lean_object* v_a_2738_; lean_object* v_fst_2739_; lean_object* v_found_2740_; size_t v___x_2741_; size_t v___x_2742_; 
v_a_2738_ = lean_array_uget_borrowed(v_as_2731_, v_i_2733_);
v_fst_2739_ = lean_ctor_get(v_a_2738_, 0);
lean_inc(v_fst_2739_);
v_found_2740_ = l_Lean_NameSet_insert(v_b_2734_, v_fst_2739_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2733_, v___x_2741_);
v_i_2733_ = v___x_2742_;
v_b_2734_ = v_found_2740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2744_, lean_object* v_sz_2745_, lean_object* v_i_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_){
_start:
{
size_t v_sz_boxed_2749_; size_t v_i_boxed_2750_; lean_object* v_res_2751_; 
v_sz_boxed_2749_ = lean_unbox_usize(v_sz_2745_);
lean_dec(v_sz_2745_);
v_i_boxed_2750_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2744_, v_sz_boxed_2749_, v_i_boxed_2750_, v_b_2747_);
lean_dec_ref(v_as_2744_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2752_, size_t v_sz_2753_, size_t v_i_2754_, lean_object* v_b_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = lean_usize_dec_lt(v_i_2754_, v_sz_2753_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_b_2755_);
return v___x_2760_;
}
else
{
lean_object* v_a_2761_; size_t v_sz_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v_a_2761_ = lean_array_uget_borrowed(v_as_2752_, v_i_2754_);
v_sz_2762_ = lean_array_size(v_a_2761_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2761_, v_sz_2762_, v___x_2763_, v_b_2755_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; size_t v___x_2766_; size_t v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2754_, v___x_2766_);
v_i_2754_ = v___x_2767_;
v_b_2755_ = v_a_2765_;
goto _start;
}
else
{
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2769_, lean_object* v_sz_2770_, lean_object* v_i_2771_, lean_object* v_b_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
size_t v_sz_boxed_2776_; size_t v_i_boxed_2777_; lean_object* v_res_2778_; 
v_sz_boxed_2776_ = lean_unbox_usize(v_sz_2770_);
lean_dec(v_sz_2770_);
v_i_boxed_2777_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2769_, v_sz_boxed_2776_, v_i_boxed_2777_, v_b_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v_as_2769_);
return v_res_2778_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2779_, lean_object* v_x1_2780_, lean_object* v_x2_2781_){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = l_Lean_Name_toString(v_x1_2780_, v___x_2779_);
v___x_2783_ = l_Lean_Name_toString(v_x2_2781_, v___x_2779_);
v___x_2784_ = lean_string_dec_lt(v___x_2782_, v___x_2783_);
lean_dec_ref(v___x_2783_);
lean_dec_ref(v___x_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2785_, lean_object* v_x1_2786_, lean_object* v_x2_2787_){
_start:
{
uint8_t v___x_7607__boxed_2788_; uint8_t v_res_2789_; lean_object* v_r_2790_; 
v___x_7607__boxed_2788_ = lean_unbox(v___x_2785_);
v_res_2789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_7607__boxed_2788_, v_x1_2786_, v_x2_2787_);
v_r_2790_ = lean_box(v_res_2789_);
return v_r_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(lean_object* v_hi_2791_, lean_object* v_pivot_2792_, lean_object* v_as_2793_, lean_object* v_i_2794_, lean_object* v_k_2795_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_nat_dec_lt(v_k_2795_, v_hi_2791_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec(v_k_2795_);
lean_dec(v_pivot_2792_);
v___x_2797_ = lean_array_fswap(v_as_2793_, v_i_2794_, v_hi_2791_);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v_i_2794_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2799_ = lean_array_fget_borrowed(v_as_2793_, v_k_2795_);
lean_inc(v___x_2799_);
v___x_2800_ = l_Lean_Name_toString(v___x_2799_, v___x_2796_);
lean_inc(v_pivot_2792_);
v___x_2801_ = l_Lean_Name_toString(v_pivot_2792_, v___x_2796_);
v___x_2802_ = lean_string_dec_lt(v___x_2800_, v___x_2801_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v___x_2800_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_unsigned_to_nat(1u);
v___x_2804_ = lean_nat_add(v_k_2795_, v___x_2803_);
lean_dec(v_k_2795_);
v_k_2795_ = v___x_2804_;
goto _start;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = lean_array_fswap(v_as_2793_, v_i_2794_, v_k_2795_);
v___x_2807_ = lean_unsigned_to_nat(1u);
v___x_2808_ = lean_nat_add(v_i_2794_, v___x_2807_);
lean_dec(v_i_2794_);
v___x_2809_ = lean_nat_add(v_k_2795_, v___x_2807_);
lean_dec(v_k_2795_);
v_as_2793_ = v___x_2806_;
v_i_2794_ = v___x_2808_;
v_k_2795_ = v___x_2809_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_hi_2811_, lean_object* v_pivot_2812_, lean_object* v_as_2813_, lean_object* v_i_2814_, lean_object* v_k_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2811_, v_pivot_2812_, v_as_2813_, v_i_2814_, v_k_2815_);
lean_dec(v_hi_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_n_2817_, lean_object* v_as_2818_, lean_object* v_lo_2819_, lean_object* v_hi_2820_){
_start:
{
lean_object* v___y_2822_; uint8_t v___x_2832_; 
v___x_2832_ = lean_nat_dec_lt(v_lo_2819_, v_hi_2820_);
if (v___x_2832_ == 0)
{
lean_dec(v_lo_2819_);
return v_as_2818_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v_mid_2835_; lean_object* v___y_2837_; lean_object* v___y_2843_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2833_ = lean_nat_add(v_lo_2819_, v_hi_2820_);
v___x_2834_ = lean_unsigned_to_nat(1u);
v_mid_2835_ = lean_nat_shiftr(v___x_2833_, v___x_2834_);
lean_dec(v___x_2833_);
v___x_2848_ = lean_array_fget_borrowed(v_as_2818_, v_mid_2835_);
v___x_2849_ = lean_array_fget_borrowed(v_as_2818_, v_lo_2819_);
lean_inc(v___x_2849_);
lean_inc(v___x_2848_);
v___x_2850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2832_, v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
v___y_2843_ = v_as_2818_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_array_fswap(v_as_2818_, v_lo_2819_, v_mid_2835_);
v___y_2843_ = v___x_2851_;
goto v___jp_2842_;
}
v___jp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_array_fget_borrowed(v___y_2837_, v_mid_2835_);
v___x_2839_ = lean_array_fget_borrowed(v___y_2837_, v_hi_2820_);
lean_inc(v___x_2839_);
lean_inc(v___x_2838_);
v___x_2840_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2832_, v___x_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_dec(v_mid_2835_);
v___y_2822_ = v___y_2837_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_array_fswap(v___y_2837_, v_mid_2835_, v_hi_2820_);
lean_dec(v_mid_2835_);
v___y_2822_ = v___x_2841_;
goto v___jp_2821_;
}
}
v___jp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2844_ = lean_array_fget_borrowed(v___y_2843_, v_hi_2820_);
v___x_2845_ = lean_array_fget_borrowed(v___y_2843_, v_lo_2819_);
lean_inc(v___x_2845_);
lean_inc(v___x_2844_);
v___x_2846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_2832_, v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
v___y_2837_ = v___y_2843_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_array_fswap(v___y_2843_, v_lo_2819_, v_hi_2820_);
v___y_2837_ = v___x_2847_;
goto v___jp_2836_;
}
}
}
v___jp_2821_:
{
lean_object* v_pivot_2823_; lean_object* v___x_2824_; lean_object* v_fst_2825_; lean_object* v_snd_2826_; uint8_t v___x_2827_; 
v_pivot_2823_ = lean_array_fget(v___y_2822_, v_hi_2820_);
lean_inc_n(v_lo_2819_, 2);
v___x_2824_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_2820_, v_pivot_2823_, v___y_2822_, v_lo_2819_, v_lo_2819_);
v_fst_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_fst_2825_);
v_snd_2826_ = lean_ctor_get(v___x_2824_, 1);
lean_inc(v_snd_2826_);
lean_dec_ref(v___x_2824_);
v___x_2827_ = lean_nat_dec_le(v_hi_2820_, v_fst_2825_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2817_, v_snd_2826_, v_lo_2819_, v_fst_2825_);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_add(v_fst_2825_, v___x_2829_);
lean_dec(v_fst_2825_);
v_as_2818_ = v___x_2828_;
v_lo_2819_ = v___x_2830_;
goto _start;
}
else
{
lean_dec(v_fst_2825_);
lean_dec(v_lo_2819_);
return v_snd_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_n_2852_, lean_object* v_as_2853_, lean_object* v_lo_2854_, lean_object* v_hi_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_2852_, v_as_2853_, v_lo_2854_, v_hi_2855_);
lean_dec(v_hi_2855_);
lean_dec(v_n_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2857_, lean_object* v_x_2858_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_object* v_k_2860_; lean_object* v_l_2861_; lean_object* v_r_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_k_2860_ = lean_ctor_get(v_x_2858_, 1);
lean_inc(v_k_2860_);
v_l_2861_ = lean_ctor_get(v_x_2858_, 3);
lean_inc(v_l_2861_);
v_r_2862_ = lean_ctor_get(v_x_2858_, 4);
lean_inc(v_r_2862_);
lean_dec_ref(v_x_2858_);
v___x_2863_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2857_, v_l_2861_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
v_a_2865_ = lean_ctor_get(v_a_2864_, 0);
lean_inc(v_a_2865_);
lean_dec(v_a_2864_);
v___x_2866_ = l_Lean_NameSet_insert(v_a_2865_, v_k_2860_);
v_init_2857_ = v___x_2866_;
v_x_2858_ = v_r_2862_;
goto _start;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_init_2857_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2870_, v_x_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v_k_2876_; lean_object* v_l_2877_; lean_object* v_r_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_k_2876_ = lean_ctor_get(v_x_2875_, 1);
lean_inc(v_k_2876_);
v_l_2877_ = lean_ctor_get(v_x_2875_, 3);
lean_inc(v_l_2877_);
v_r_2878_ = lean_ctor_get(v_x_2875_, 4);
lean_inc(v_r_2878_);
lean_dec_ref(v_x_2875_);
v___x_2879_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2874_, v_l_2877_);
v___x_2880_ = lean_array_push(v___x_2879_, v_k_2876_);
v_init_2874_ = v___x_2880_;
v_x_2875_ = v_r_2878_;
goto _start;
}
else
{
return v_init_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___y_2886_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___x_2912_; lean_object* v_env_2913_; lean_object* v___x_2914_; lean_object* v_toEnvExtension_2915_; lean_object* v_asyncMode_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_found_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_a_2923_; lean_object* v_a_2925_; lean_object* v_a_2942_; 
v___x_2912_ = lean_st_ref_get(v___y_2883_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc_ref_n(v_env_2913_, 2);
lean_dec(v___x_2912_);
v___x_2914_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2915_ = lean_ctor_get(v___x_2914_, 0);
v_asyncMode_2916_ = lean_ctor_get(v_toEnvExtension_2915_, 2);
v___x_2917_ = lean_box(1);
v___x_2918_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
v_found_2919_ = l_Lean_NameSet_empty;
v___x_2920_ = lean_box(0);
v___x_2921_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2917_, v___x_2914_, v_env_2913_, v_asyncMode_2916_, v___x_2920_);
v___x_2922_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2919_, v___x_2921_);
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2922_);
v_a_2942_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_a_2942_);
lean_dec(v_a_2923_);
v_a_2925_ = v_a_2942_;
goto v___jp_2924_;
v___jp_2885_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_array_to_list(v___y_2886_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
v___jp_2889_:
{
lean_object* v___x_2894_; 
v___x_2894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2891_, v___y_2890_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec(v___y_2891_);
v___y_2886_ = v___x_2894_;
goto v___jp_2885_;
}
v___jp_2895_:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_nat_dec_le(v___y_2899_, v___y_2897_);
if (v___x_2900_ == 0)
{
lean_dec(v___y_2897_);
lean_inc(v___y_2899_);
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2898_;
v___y_2892_ = v___y_2899_;
v___y_2893_ = v___y_2899_;
goto v___jp_2889_;
}
else
{
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2898_;
v___y_2892_ = v___y_2899_;
v___y_2893_ = v___y_2897_;
goto v___jp_2889_;
}
}
v___jp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2904_ = lean_mk_empty_array_with_capacity(v___y_2903_);
lean_dec(v___y_2903_);
v___x_2905_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2904_, v___y_2902_);
v___x_2906_ = lean_array_get_size(v___x_2905_);
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = lean_nat_dec_eq(v___x_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_sub(v___x_2906_, v___x_2909_);
v___x_2911_ = lean_nat_dec_le(v___x_2907_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_inc(v___x_2910_);
v___y_2896_ = v___x_2905_;
v___y_2897_ = v___x_2910_;
v___y_2898_ = v___x_2906_;
v___y_2899_ = v___x_2910_;
goto v___jp_2895_;
}
else
{
v___y_2896_ = v___x_2905_;
v___y_2897_ = v___x_2910_;
v___y_2898_ = v___x_2906_;
v___y_2899_ = v___x_2907_;
goto v___jp_2895_;
}
}
else
{
v___y_2886_ = v___x_2905_;
goto v___jp_2885_;
}
}
v___jp_2924_:
{
lean_object* v___x_2926_; lean_object* v_importedEntries_2927_; size_t v_sz_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2926_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2918_, v_toEnvExtension_2915_, v_env_2913_, v_asyncMode_2916_, v___x_2920_);
v_importedEntries_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref(v_importedEntries_2927_);
lean_dec(v___x_2926_);
v_sz_2928_ = lean_array_size(v_importedEntries_2927_);
v___x_2929_ = ((size_t)0ULL);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2927_, v_sz_2928_, v___x_2929_, v_a_2925_, v___y_2882_, v___y_2883_);
lean_dec_ref(v_importedEntries_2927_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref(v___x_2930_);
if (lean_obj_tag(v_a_2931_) == 0)
{
lean_object* v_size_2932_; 
v_size_2932_ = lean_ctor_get(v_a_2931_, 0);
lean_inc(v_size_2932_);
v___y_2902_ = v_a_2931_;
v___y_2903_ = v_size_2932_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_unsigned_to_nat(0u);
v___y_2902_ = v_a_2931_;
v___y_2903_ = v___x_2933_;
goto v___jp_2901_;
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_a_2934_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2930_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2930_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
return v_res_2946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2949_ = l_Lean_stringToMessageData(v___x_2948_);
return v___x_2949_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2952_ = l_Lean_stringToMessageData(v___x_2951_);
return v___x_2952_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
return v___x_2955_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2958_ = l_Lean_stringToMessageData(v___x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2965_ = l_Lean_MessageData_ofFormat(v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2970_ = l_Lean_MessageData_ofFormat(v___x_2969_);
return v___x_2970_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2974_, lean_object* v_as_2975_, size_t v_sz_2976_, size_t v_i_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_a_2983_; uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_lt(v_i_2977_, v_sz_2976_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
lean_dec(v_decl_2974_);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_b_2978_);
return v___x_2988_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_a_2989_ = lean_array_uget_borrowed(v_as_2975_, v_i_2977_);
v___x_2990_ = l_Lean_TSyntax_getId(v_a_2989_);
lean_inc(v___x_2990_);
v___x_2991_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2990_, v___y_2980_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_box(0);
if (lean_obj_tag(v_a_2992_) == 1)
{
lean_object* v___x_2994_; lean_object* v_env_2995_; lean_object* v_nextMacroScope_2996_; lean_object* v_ngen_2997_; lean_object* v_auxDeclNGen_2998_; lean_object* v_traceState_2999_; lean_object* v_messages_3000_; lean_object* v_infoState_3001_; lean_object* v_snapshotTasks_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_a_2992_);
v___x_2994_ = lean_st_ref_take(v___y_2980_);
v_env_2995_ = lean_ctor_get(v___x_2994_, 0);
v_nextMacroScope_2996_ = lean_ctor_get(v___x_2994_, 1);
v_ngen_2997_ = lean_ctor_get(v___x_2994_, 2);
v_auxDeclNGen_2998_ = lean_ctor_get(v___x_2994_, 3);
v_traceState_2999_ = lean_ctor_get(v___x_2994_, 4);
v_messages_3000_ = lean_ctor_get(v___x_2994_, 6);
v_infoState_3001_ = lean_ctor_get(v___x_2994_, 7);
v_snapshotTasks_3002_ = lean_ctor_get(v___x_2994_, 8);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_2994_, 5);
lean_dec(v_unused_3018_);
v___x_3004_ = v___x_2994_;
v_isShared_3005_ = v_isSharedCheck_3017_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_snapshotTasks_3002_);
lean_inc(v_infoState_3001_);
lean_inc(v_messages_3000_);
lean_inc(v_traceState_2999_);
lean_inc(v_auxDeclNGen_2998_);
lean_inc(v_ngen_2997_);
lean_inc(v_nextMacroScope_2996_);
lean_inc(v_env_2995_);
lean_dec(v___x_2994_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3017_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v_toEnvExtension_3007_; lean_object* v_asyncMode_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3006_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3007_ = lean_ctor_get(v___x_3006_, 0);
v_asyncMode_3008_ = lean_ctor_get(v_toEnvExtension_3007_, 2);
v___x_3009_ = lean_box(0);
lean_inc(v_decl_2974_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_decl_2974_);
lean_ctor_set(v___x_3010_, 1, v___x_2990_);
v___x_3011_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3006_, v_env_2995_, v___x_3010_, v_asyncMode_3008_, v___x_3009_);
v___x_3012_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 5, v___x_3012_);
lean_ctor_set(v___x_3004_, 0, v___x_3011_);
v___x_3014_ = v___x_3004_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_nextMacroScope_2996_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_ngen_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_auxDeclNGen_2998_);
lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_traceState_2999_);
lean_ctor_set(v_reuseFailAlloc_3016_, 5, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3016_, 6, v_messages_3000_);
lean_ctor_set(v_reuseFailAlloc_3016_, 7, v_infoState_3001_);
lean_ctor_set(v_reuseFailAlloc_3016_, 8, v_snapshotTasks_3002_);
v___x_3014_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_st_ref_set(v___y_2980_, v___x_3014_);
v_a_2983_ = v___x_2993_;
goto v___jp_2982_;
}
}
}
else
{
lean_object* v___x_3019_; 
lean_dec(v_a_2992_);
v___x_3019_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2979_, v___y_2980_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___y_3022_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
v___x_3034_ = lean_unsigned_to_nat(0u);
v___x_3035_ = l_List_lengthTR___redArg(v_a_3020_);
v___x_3036_ = lean_nat_dec_eq(v___x_3035_, v___x_3034_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_dec_eq(v___x_3035_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3039_ = lean_unsigned_to_nat(10u);
v___x_3040_ = lean_nat_dec_lt(v___x_3035_, v___x_3039_);
lean_dec(v___x_3035_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3041_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_3020_);
v___x_3043_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_3020_, v_a_3020_, v___x_3039_, v___x_3042_);
lean_dec(v_a_3020_);
v___x_3044_ = lean_box(0);
v___x_3045_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_3043_, v___x_3044_);
v___x_3046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3047_ = l_Lean_MessageData_joinSep(v___x_3045_, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3041_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_3050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___y_3022_ = v___x_3050_;
goto v___jp_3021_;
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3051_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_3052_ = lean_box(0);
v___x_3053_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3020_, v___x_3052_);
v___x_3054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3055_ = l_Lean_MessageData_joinSep(v___x_3053_, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3051_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___y_3022_ = v___x_3056_;
goto v___jp_3021_;
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_dec(v___x_3035_);
v___x_3057_ = lean_box(0);
v___x_3058_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_3020_, v___x_3057_);
v___x_3059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_3060_ = l_Lean_MessageData_joinSep(v___x_3058_, v___x_3059_);
v___y_3022_ = v___x_3060_;
goto v___jp_3021_;
}
}
else
{
lean_object* v___x_3061_; 
lean_dec(v___x_3035_);
lean_dec(v_a_3020_);
v___x_3061_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_3022_ = v___x_3061_;
goto v___jp_3021_;
}
v___jp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v___y_3022_);
v___x_3025_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_3028_ = l_Lean_MessageData_ofName(v___x_2990_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3026_);
v___x_3033_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_a_2989_, v___x_3032_, v___y_2979_, v___y_2980_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec_ref(v___x_3033_);
v_a_2983_ = v___x_2993_;
goto v___jp_2982_;
}
else
{
lean_dec(v_decl_2974_);
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_2990_);
lean_dec(v_decl_2974_);
v_a_3062_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3019_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3019_);
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
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___x_2990_);
lean_dec(v_decl_2974_);
v_a_3070_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2991_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2991_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
v___jp_2982_:
{
size_t v___x_2984_; size_t v___x_2985_; 
v___x_2984_ = ((size_t)1ULL);
v___x_2985_ = lean_usize_add(v_i_2977_, v___x_2984_);
v_i_2977_ = v___x_2985_;
v_b_2978_ = v_a_2983_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_3078_, lean_object* v_as_3079_, lean_object* v_sz_3080_, lean_object* v_i_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
size_t v_sz_boxed_3086_; size_t v_i_boxed_3087_; lean_object* v_res_3088_; 
v_sz_boxed_3086_ = lean_unbox_usize(v_sz_3080_);
lean_dec(v_sz_3080_);
v_i_boxed_3087_ = lean_unbox_usize(v_i_3081_);
lean_dec(v_i_3081_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3078_, v_as_3079_, v_sz_boxed_3086_, v_i_boxed_3087_, v_b_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_as_3079_);
return v_res_3088_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3091_ = l_Lean_stringToMessageData(v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_3092_, lean_object* v___x_3093_, lean_object* v___x_3094_, lean_object* v_name_3095_, lean_object* v_decl_3096_, lean_object* v_stx_3097_, uint8_t v_kind_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = 0;
v___x_3163_ = l_Lean_instBEqAttributeKind_beq(v_kind_3098_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
lean_dec(v_stx_3097_);
lean_dec(v_decl_3096_);
lean_dec_ref(v___x_3094_);
lean_dec_ref(v___x_3093_);
lean_dec_ref(v___x_3092_);
v___x_3164_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_3095_, v_kind_3098_, v___y_3099_, v___y_3100_);
return v___x_3164_;
}
else
{
goto v___jp_3136_;
}
v___jp_3102_:
{
lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3106_ = lean_box(0);
v_sz_3107_ = lean_array_size(v___y_3103_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_3096_, v___y_3103_, v_sz_3107_, v___x_3108_, v___x_3106_, v___y_3104_, v___y_3105_);
lean_dec_ref(v___y_3103_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3109_, 0);
lean_dec(v_unused_3117_);
v___x_3111_ = v___x_3109_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v___x_3109_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3106_);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3106_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
return v___x_3109_;
}
}
v___jp_3118_:
{
lean_object* v___x_3122_; lean_object* v_env_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_st_ref_get(v___y_3121_);
v_env_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc_ref(v_env_3123_);
lean_dec(v___x_3122_);
lean_inc(v_decl_3096_);
v___x_3124_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3123_, v_decl_3096_);
if (lean_obj_tag(v___x_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v___y_3119_);
v_val_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_val_3125_);
lean_dec_ref(v___x_3124_);
v___x_3126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_MessageData_ofConstName(v_decl_3096_, v___x_3127_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3126_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Lean_MessageData_ofConstName(v_val_3125_, v___x_3127_);
v___x_3133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3131_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3126_);
v___x_3135_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3097_, v___x_3134_, v___y_3120_, v___y_3121_);
lean_dec(v_stx_3097_);
return v___x_3135_;
}
else
{
lean_dec(v___x_3124_);
lean_dec(v_stx_3097_);
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___y_3120_;
v___y_3105_ = v___y_3121_;
goto v___jp_3102_;
}
}
v___jp_3136_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_3138_ = l_Lean_Name_mkStr4(v___x_3092_, v___x_3093_, v___x_3137_, v___x_3094_);
lean_inc(v_stx_3097_);
v___x_3139_ = l_Lean_Syntax_isOfKind(v_stx_3097_, v___x_3138_);
lean_dec(v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec(v_stx_3097_);
lean_dec(v_decl_3096_);
v___x_3140_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3141_ = l_Lean_MessageData_ofName(v_name_3095_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_3144_, v___y_3099_, v___y_3100_);
return v___x_3145_;
}
else
{
lean_object* v___x_3146_; lean_object* v_env_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v_tags_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v_name_3095_);
v___x_3146_ = lean_st_ref_get(v___y_3100_);
v_env_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3146_);
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = l_Lean_Syntax_getArg(v_stx_3097_, v___x_3148_);
v_tags_3150_ = l_Lean_Syntax_getArgs(v___x_3149_);
lean_dec(v___x_3149_);
v___x_3151_ = 0;
lean_inc(v_decl_3096_);
v___x_3152_ = l_Lean_Environment_find_x3f(v_env_3147_, v_decl_3096_, v___x_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
v___y_3119_ = v_tags_3150_;
v___y_3120_ = v___y_3099_;
v___y_3121_ = v___y_3100_;
goto v___jp_3118_;
}
else
{
lean_dec_ref(v___x_3152_);
if (v___x_3139_ == 0)
{
v___y_3119_ = v_tags_3150_;
v___y_3120_ = v___y_3099_;
v___y_3121_ = v___y_3100_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3153_; lean_object* v_env_3154_; uint8_t v___x_3155_; 
v___x_3153_ = lean_st_ref_get(v___y_3100_);
v_env_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_env_3154_);
lean_dec(v___x_3153_);
v___x_3155_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_3154_, v_decl_3096_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec_ref(v_tags_3150_);
v___x_3156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3157_ = l_Lean_MessageData_ofConstName(v_decl_3096_, v___x_3151_);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3097_, v___x_3160_, v___y_3099_, v___y_3100_);
lean_dec(v_stx_3097_);
return v___x_3161_;
}
else
{
v___y_3119_ = v_tags_3150_;
v___y_3120_ = v___y_3099_;
v___y_3121_ = v___y_3100_;
goto v___jp_3118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_3165_, lean_object* v___x_3166_, lean_object* v___x_3167_, lean_object* v_name_3168_, lean_object* v_decl_3169_, lean_object* v_stx_3170_, lean_object* v_kind_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_kind_boxed_3175_; lean_object* v_res_3176_; 
v_kind_boxed_3175_ = lean_unbox(v_kind_3171_);
v_res_3176_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_3165_, v___x_3166_, v___x_3167_, v_name_3168_, v_decl_3169_, v_stx_3170_, v_kind_boxed_3175_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3211_ = l_Lean_registerBuiltinAttribute(v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_3214_, v___y_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_3224_, lean_object* v_k_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_, lean_object* v_x_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3224_, v_k_3225_, v_x_3226_, v_x_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_3230_, lean_object* v_k_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_3230_, v_k_3231_, v_x_3232_, v_x_3233_, v_x_3234_);
lean_dec_ref(v_k_3231_);
lean_dec_ref(v_as_3230_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_3236_, size_t v_sz_3237_, size_t v_i_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_3236_, v_sz_3237_, v_i_3238_, v_b_3239_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_3244_, lean_object* v_sz_3245_, lean_object* v_i_3246_, lean_object* v_b_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
size_t v_sz_boxed_3251_; size_t v_i_boxed_3252_; lean_object* v_res_3253_; 
v_sz_boxed_3251_ = lean_unbox_usize(v_sz_3245_);
lean_dec(v_sz_3245_);
v_i_boxed_3252_ = lean_unbox_usize(v_i_3246_);
lean_dec(v_i_3246_);
v_res_3253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_3244_, v_sz_boxed_3251_, v_i_boxed_3252_, v_b_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v_as_3244_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_3254_, lean_object* v_t_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_3254_, v_t_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_3257_, lean_object* v_as_3258_, lean_object* v_lo_3259_, lean_object* v_hi_3260_, lean_object* v_w_3261_, lean_object* v_hlo_3262_, lean_object* v_hhi_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_n_3257_, v_as_3258_, v_lo_3259_, v_hi_3260_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_3265_, lean_object* v_as_3266_, lean_object* v_lo_3267_, lean_object* v_hi_3268_, lean_object* v_w_3269_, lean_object* v_hlo_3270_, lean_object* v_hhi_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_3265_, v_as_3266_, v_lo_3267_, v_hi_3268_, v_w_3269_, v_hlo_3270_, v_hhi_3271_);
lean_dec(v_hi_3268_);
lean_dec(v_n_3265_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_3273_, lean_object* v_x_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_3273_, v_x_3274_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_3279_, lean_object* v_x_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_3279_, v_x_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(lean_object* v_n_3285_, lean_object* v_lo_3286_, lean_object* v_hi_3287_, lean_object* v_hhi_3288_, lean_object* v_pivot_3289_, lean_object* v_as_3290_, lean_object* v_i_3291_, lean_object* v_k_3292_, lean_object* v_ilo_3293_, lean_object* v_ik_3294_, lean_object* v_w_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___redArg(v_hi_3287_, v_pivot_3289_, v_as_3290_, v_i_3291_, v_k_3292_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7___boxed(lean_object* v_n_3297_, lean_object* v_lo_3298_, lean_object* v_hi_3299_, lean_object* v_hhi_3300_, lean_object* v_pivot_3301_, lean_object* v_as_3302_, lean_object* v_i_3303_, lean_object* v_k_3304_, lean_object* v_ilo_3305_, lean_object* v_ik_3306_, lean_object* v_w_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5_spec__7(v_n_3297_, v_lo_3298_, v_hi_3299_, v_hhi_3300_, v_pivot_3301_, v_as_3302_, v_i_3303_, v_k_3304_, v_ilo_3305_, v_ik_3306_, v_w_3307_);
lean_dec(v_hi_3299_);
lean_dec(v_lo_3298_);
lean_dec(v_n_3297_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_fst_3313_ = lean_ctor_get(v_x_3312_, 0);
lean_inc(v_fst_3313_);
v_snd_3314_ = lean_ctor_get(v_x_3312_, 1);
lean_inc(v_snd_3314_);
lean_dec_ref(v_x_3312_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3316_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3311_, v_fst_3313_, v___x_3315_);
v___x_3317_ = lean_array_push(v___x_3316_, v_snd_3314_);
v___x_3318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3313_, v___x_3317_, v_es_3311_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3319_, lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 0)
{
lean_object* v_k_3321_; lean_object* v_v_3322_; lean_object* v_l_3323_; lean_object* v_r_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_k_3321_ = lean_ctor_get(v_x_3320_, 1);
v_v_3322_ = lean_ctor_get(v_x_3320_, 2);
v_l_3323_ = lean_ctor_get(v_x_3320_, 3);
v_r_3324_ = lean_ctor_get(v_x_3320_, 4);
v___x_3325_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3319_, v_l_3323_);
lean_inc(v_v_3322_);
lean_inc(v_k_3321_);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_k_3321_);
lean_ctor_set(v___x_3326_, 1, v_v_3322_);
v___x_3327_ = lean_array_push(v___x_3325_, v___x_3326_);
v_init_3319_ = v___x_3327_;
v_x_3320_ = v_r_3324_;
goto _start;
}
else
{
return v_init_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3329_, v_x_3330_);
lean_dec(v_x_3330_);
return v_res_3331_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3332_, lean_object* v_x2_3333_){
_start:
{
lean_object* v_fst_3334_; lean_object* v_fst_3335_; uint8_t v___x_3336_; 
v_fst_3334_ = lean_ctor_get(v_x1_3332_, 0);
v_fst_3335_ = lean_ctor_get(v_x2_3333_, 0);
v___x_3336_ = l_Lean_Name_quickLt(v_fst_3334_, v_fst_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3337_, lean_object* v_x2_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3337_, v_x2_3338_);
lean_dec_ref(v_x2_3338_);
lean_dec_ref(v_x1_3337_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3341_, lean_object* v_pivot_3342_, lean_object* v_as_3343_, lean_object* v_i_3344_, lean_object* v_k_3345_){
_start:
{
uint8_t v___x_3346_; 
v___x_3346_ = lean_nat_dec_lt(v_k_3345_, v_hi_3341_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v_k_3345_);
v___x_3347_ = lean_array_fswap(v_as_3343_, v_i_3344_, v_hi_3341_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_i_3344_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; lean_object* v_fst_3350_; lean_object* v_fst_3351_; uint8_t v___x_3352_; 
v___x_3349_ = lean_array_fget_borrowed(v_as_3343_, v_k_3345_);
v_fst_3350_ = lean_ctor_get(v___x_3349_, 0);
v_fst_3351_ = lean_ctor_get(v_pivot_3342_, 0);
v___x_3352_ = l_Lean_Name_quickLt(v_fst_3350_, v_fst_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_add(v_k_3345_, v___x_3353_);
lean_dec(v_k_3345_);
v_k_3345_ = v___x_3354_;
goto _start;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3356_ = lean_array_fswap(v_as_3343_, v_i_3344_, v_k_3345_);
v___x_3357_ = lean_unsigned_to_nat(1u);
v___x_3358_ = lean_nat_add(v_i_3344_, v___x_3357_);
lean_dec(v_i_3344_);
v___x_3359_ = lean_nat_add(v_k_3345_, v___x_3357_);
lean_dec(v_k_3345_);
v_as_3343_ = v___x_3356_;
v_i_3344_ = v___x_3358_;
v_k_3345_ = v___x_3359_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3361_, lean_object* v_pivot_3362_, lean_object* v_as_3363_, lean_object* v_i_3364_, lean_object* v_k_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3361_, v_pivot_3362_, v_as_3363_, v_i_3364_, v_k_3365_);
lean_dec_ref(v_pivot_3362_);
lean_dec(v_hi_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3367_, lean_object* v_as_3368_, lean_object* v_lo_3369_, lean_object* v_hi_3370_){
_start:
{
lean_object* v___y_3372_; uint8_t v___x_3382_; 
v___x_3382_ = lean_nat_dec_lt(v_lo_3369_, v_hi_3370_);
if (v___x_3382_ == 0)
{
lean_dec(v_lo_3369_);
return v_as_3368_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v_mid_3385_; lean_object* v___y_3387_; lean_object* v___y_3393_; lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3383_ = lean_nat_add(v_lo_3369_, v_hi_3370_);
v___x_3384_ = lean_unsigned_to_nat(1u);
v_mid_3385_ = lean_nat_shiftr(v___x_3383_, v___x_3384_);
lean_dec(v___x_3383_);
v___x_3398_ = lean_array_fget_borrowed(v_as_3368_, v_mid_3385_);
v___x_3399_ = lean_array_fget_borrowed(v_as_3368_, v_lo_3369_);
v___x_3400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3398_, v___x_3399_);
if (v___x_3400_ == 0)
{
v___y_3393_ = v_as_3368_;
goto v___jp_3392_;
}
else
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_array_fswap(v_as_3368_, v_lo_3369_, v_mid_3385_);
v___y_3393_ = v___x_3401_;
goto v___jp_3392_;
}
v___jp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3388_ = lean_array_fget_borrowed(v___y_3387_, v_mid_3385_);
v___x_3389_ = lean_array_fget_borrowed(v___y_3387_, v_hi_3370_);
v___x_3390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_dec(v_mid_3385_);
v___y_3372_ = v___y_3387_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_array_fswap(v___y_3387_, v_mid_3385_, v_hi_3370_);
lean_dec(v_mid_3385_);
v___y_3372_ = v___x_3391_;
goto v___jp_3371_;
}
}
v___jp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3394_ = lean_array_fget_borrowed(v___y_3393_, v_hi_3370_);
v___x_3395_ = lean_array_fget_borrowed(v___y_3393_, v_lo_3369_);
v___x_3396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3394_, v___x_3395_);
if (v___x_3396_ == 0)
{
v___y_3387_ = v___y_3393_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_array_fswap(v___y_3393_, v_lo_3369_, v_hi_3370_);
v___y_3387_ = v___x_3397_;
goto v___jp_3386_;
}
}
}
v___jp_3371_:
{
lean_object* v_pivot_3373_; lean_object* v___x_3374_; lean_object* v_fst_3375_; lean_object* v_snd_3376_; uint8_t v___x_3377_; 
v_pivot_3373_ = lean_array_fget(v___y_3372_, v_hi_3370_);
lean_inc_n(v_lo_3369_, 2);
v___x_3374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3370_, v_pivot_3373_, v___y_3372_, v_lo_3369_, v_lo_3369_);
lean_dec(v_pivot_3373_);
v_fst_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_fst_3375_);
v_snd_3376_ = lean_ctor_get(v___x_3374_, 1);
lean_inc(v_snd_3376_);
lean_dec_ref(v___x_3374_);
v___x_3377_ = lean_nat_dec_le(v_hi_3370_, v_fst_3375_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3367_, v_snd_3376_, v_lo_3369_, v_fst_3375_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_nat_add(v_fst_3375_, v___x_3379_);
lean_dec(v_fst_3375_);
v_as_3368_ = v___x_3378_;
v_lo_3369_ = v___x_3380_;
goto _start;
}
else
{
lean_dec(v_fst_3375_);
lean_dec(v_lo_3369_);
return v_snd_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3402_, lean_object* v_as_3403_, lean_object* v_lo_3404_, lean_object* v_hi_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3402_, v_as_3403_, v_lo_3404_, v_hi_3405_);
lean_dec(v_hi_3405_);
lean_dec(v_n_3402_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3409_, lean_object* v_s_3410_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___y_3416_; lean_object* v___y_3417_; uint8_t v___x_3420_; 
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3412_, v_s_3410_);
v___x_3414_ = lean_array_get_size(v___x_3413_);
v___x_3420_ = lean_nat_dec_eq(v___x_3414_, v___x_3411_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___y_3424_; uint8_t v___x_3426_; 
v___x_3421_ = lean_unsigned_to_nat(1u);
v___x_3422_ = lean_nat_sub(v___x_3414_, v___x_3421_);
v___x_3426_ = lean_nat_dec_le(v___x_3411_, v___x_3422_);
if (v___x_3426_ == 0)
{
lean_inc(v___x_3422_);
v___y_3424_ = v___x_3422_;
goto v___jp_3423_;
}
else
{
v___y_3424_ = v___x_3411_;
goto v___jp_3423_;
}
v___jp_3423_:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_nat_dec_le(v___y_3424_, v___x_3422_);
if (v___x_3425_ == 0)
{
lean_dec(v___x_3422_);
lean_inc(v___y_3424_);
v___y_3416_ = v___y_3424_;
v___y_3417_ = v___y_3424_;
goto v___jp_3415_;
}
else
{
v___y_3416_ = v___y_3424_;
v___y_3417_ = v___x_3422_;
goto v___jp_3415_;
}
}
}
else
{
lean_object* v___x_3427_; 
lean_inc_ref_n(v___x_3413_, 2);
v___x_3427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3413_);
lean_ctor_set(v___x_3427_, 1, v___x_3413_);
lean_ctor_set(v___x_3427_, 2, v___x_3413_);
return v___x_3427_;
}
v___jp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3414_, v___x_3413_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_inc_ref_n(v___x_3418_, 2);
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
lean_ctor_set(v___x_3419_, 2, v___x_3418_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3428_, lean_object* v_s_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3428_, v_s_3429_);
lean_dec(v_s_3429_);
lean_dec_ref(v_x_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3431_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3433_, v_es_3431_);
v___x_3435_ = lean_array_get_size(v___x_3434_);
v___x_3436_ = lean_nat_dec_eq(v___x_3435_, v___x_3432_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___y_3440_; uint8_t v___x_3444_; 
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_sub(v___x_3435_, v___x_3437_);
v___x_3444_ = lean_nat_dec_le(v___x_3432_, v___x_3438_);
if (v___x_3444_ == 0)
{
lean_inc(v___x_3438_);
v___y_3440_ = v___x_3438_;
goto v___jp_3439_;
}
else
{
v___y_3440_ = v___x_3432_;
goto v___jp_3439_;
}
v___jp_3439_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_le(v___y_3440_, v___x_3438_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
lean_dec(v___x_3438_);
lean_inc(v___y_3440_);
v___x_3442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3435_, v___x_3434_, v___y_3440_, v___y_3440_);
lean_dec(v___y_3440_);
return v___x_3442_;
}
else
{
lean_object* v___x_3443_; 
v___x_3443_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3435_, v___x_3434_, v___y_3440_, v___x_3438_);
lean_dec(v___x_3438_);
return v___x_3443_;
}
}
}
else
{
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3445_);
lean_dec(v_es_3445_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3447_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3452_, lean_object* v_x_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3452_, v_x_3453_, v___y_3454_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v_x_3453_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3483_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3486_, lean_object* v_t_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3486_, v_t_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3489_, lean_object* v_t_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3489_, v_t_3490_);
lean_dec(v_t_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3492_, lean_object* v_as_3493_, lean_object* v_lo_3494_, lean_object* v_hi_3495_, lean_object* v_w_3496_, lean_object* v_hlo_3497_, lean_object* v_hhi_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_n_3492_, v_as_3493_, v_lo_3494_, v_hi_3495_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3500_, lean_object* v_as_3501_, lean_object* v_lo_3502_, lean_object* v_hi_3503_, lean_object* v_w_3504_, lean_object* v_hlo_3505_, lean_object* v_hhi_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3500_, v_as_3501_, v_lo_3502_, v_hi_3503_, v_w_3504_, v_hlo_3505_, v_hhi_3506_);
lean_dec(v_hi_3503_);
lean_dec(v_n_3500_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_3508_, lean_object* v_lo_3509_, lean_object* v_hi_3510_, lean_object* v_hhi_3511_, lean_object* v_pivot_3512_, lean_object* v_as_3513_, lean_object* v_i_3514_, lean_object* v_k_3515_, lean_object* v_ilo_3516_, lean_object* v_ik_3517_, lean_object* v_w_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3510_, v_pivot_3512_, v_as_3513_, v_i_3514_, v_k_3515_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_3520_, lean_object* v_lo_3521_, lean_object* v_hi_3522_, lean_object* v_hhi_3523_, lean_object* v_pivot_3524_, lean_object* v_as_3525_, lean_object* v_i_3526_, lean_object* v_k_3527_, lean_object* v_ilo_3528_, lean_object* v_ik_3529_, lean_object* v_w_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1_spec__2(v_n_3520_, v_lo_3521_, v_hi_3522_, v_hhi_3523_, v_pivot_3524_, v_as_3525_, v_i_3526_, v_k_3527_, v_ilo_3528_, v_ik_3529_, v_w_3530_);
lean_dec_ref(v_pivot_3524_);
lean_dec(v_hi_3522_);
lean_dec(v_lo_3521_);
lean_dec(v_n_3520_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3532_, lean_object* v_k_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v_m_3538_; lean_object* v_a_3539_; uint8_t v___x_3540_; 
v___x_3536_ = lean_nat_add(v_x_3534_, v_x_3535_);
v___x_3537_ = lean_unsigned_to_nat(1u);
v_m_3538_ = lean_nat_shiftr(v___x_3536_, v___x_3537_);
lean_dec(v___x_3536_);
v_a_3539_ = lean_array_fget_borrowed(v_as_3532_, v_m_3538_);
v___x_3540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3539_, v_k_3533_);
if (v___x_3540_ == 0)
{
uint8_t v___x_3541_; 
lean_dec(v_x_3535_);
v___x_3541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3533_, v_a_3539_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_m_3538_);
lean_dec(v_x_3534_);
lean_inc(v_a_3539_);
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v_a_3539_);
return v___x_3542_;
}
else
{
lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_nat_dec_eq(v_m_3538_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; uint8_t v___x_3546_; 
v___x_3545_ = lean_nat_sub(v_m_3538_, v___x_3537_);
lean_dec(v_m_3538_);
v___x_3546_ = lean_nat_dec_lt(v___x_3545_, v_x_3534_);
if (v___x_3546_ == 0)
{
v_x_3535_ = v___x_3545_;
goto _start;
}
else
{
lean_object* v___x_3548_; 
lean_dec(v___x_3545_);
lean_dec(v_x_3534_);
v___x_3548_ = lean_box(0);
return v___x_3548_;
}
}
else
{
lean_object* v___x_3549_; 
lean_dec(v_m_3538_);
lean_dec(v_x_3534_);
v___x_3549_ = lean_box(0);
return v___x_3549_;
}
}
}
else
{
lean_object* v___x_3550_; uint8_t v___x_3551_; 
lean_dec(v_x_3534_);
v___x_3550_ = lean_nat_add(v_m_3538_, v___x_3537_);
lean_dec(v_m_3538_);
v___x_3551_ = lean_nat_dec_le(v___x_3550_, v_x_3535_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_dec(v___x_3550_);
lean_dec(v_x_3535_);
v___x_3552_ = lean_box(0);
return v___x_3552_;
}
else
{
v_x_3534_ = v___x_3550_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3554_, lean_object* v_k_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3554_, v_k_3555_, v_x_3556_, v_x_3557_);
lean_dec_ref(v_k_3555_);
lean_dec_ref(v_as_3554_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3559_, lean_object* v_as_3560_, size_t v_sz_3561_, size_t v_i_3562_, lean_object* v_b_3563_){
_start:
{
lean_object* v_a_3565_; uint8_t v___x_3569_; 
v___x_3569_ = lean_usize_dec_lt(v_i_3562_, v_sz_3561_);
if (v___x_3569_ == 0)
{
lean_dec(v_tactic_3559_);
return v_b_3563_;
}
else
{
lean_object* v___x_3570_; lean_object* v_a_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3570_ = lean_unsigned_to_nat(0u);
v_a_3571_ = lean_array_uget_borrowed(v_as_3560_, v_i_3562_);
v___x_3572_ = lean_array_get_size(v_a_3571_);
v___x_3573_ = lean_nat_dec_lt(v___x_3570_, v___x_3572_);
if (v___x_3573_ == 0)
{
v_a_3565_ = v_b_3563_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3574_ = lean_unsigned_to_nat(1u);
v___x_3575_ = lean_nat_sub(v___x_3572_, v___x_3574_);
v___x_3576_ = lean_nat_dec_le(v___x_3570_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_dec(v___x_3575_);
v_a_3565_ = v_b_3563_;
goto v___jp_3564_;
}
else
{
lean_object* v_extensions_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_extensions_3577_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3559_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_tactic_3559_);
lean_ctor_set(v___x_3578_, 1, v_extensions_3577_);
v___x_3579_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3571_, v___x_3578_, v___x_3570_, v___x_3575_);
lean_dec_ref(v___x_3578_);
if (lean_obj_tag(v___x_3579_) == 1)
{
lean_object* v_val_3580_; lean_object* v_snd_3581_; lean_object* v___x_3582_; 
v_val_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3580_);
lean_dec_ref(v___x_3579_);
v_snd_3581_ = lean_ctor_get(v_val_3580_, 1);
lean_inc(v_snd_3581_);
lean_dec(v_val_3580_);
v___x_3582_ = l_Array_append___redArg(v_b_3563_, v_snd_3581_);
lean_dec(v_snd_3581_);
v_a_3565_ = v___x_3582_;
goto v___jp_3564_;
}
else
{
lean_dec(v___x_3579_);
v_a_3565_ = v_b_3563_;
goto v___jp_3564_;
}
}
}
}
v___jp_3564_:
{
size_t v___x_3566_; size_t v___x_3567_; 
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_add(v_i_3562_, v___x_3566_);
v_i_3562_ = v___x_3567_;
v_b_3563_ = v_a_3565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3583_, lean_object* v_as_3584_, lean_object* v_sz_3585_, lean_object* v_i_3586_, lean_object* v_b_3587_){
_start:
{
size_t v_sz_boxed_3588_; size_t v_i_boxed_3589_; lean_object* v_res_3590_; 
v_sz_boxed_3588_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v_i_boxed_3589_ = lean_unbox_usize(v_i_3586_);
lean_dec(v_i_3586_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3583_, v_as_3584_, v_sz_boxed_3588_, v_i_boxed_3589_, v_b_3587_);
lean_dec_ref(v_as_3584_);
return v_res_3590_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_box(1);
v___x_3592_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3593_, lean_object* v_tactic_3594_){
_start:
{
lean_object* v___x_3595_; lean_object* v_toEnvExtension_3596_; lean_object* v_asyncMode_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_importedEntries_3602_; lean_object* v_extensions_3603_; size_t v_sz_3604_; size_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3595_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3596_ = lean_ctor_get(v___x_3595_, 0);
v_asyncMode_3597_ = lean_ctor_get(v_toEnvExtension_3596_, 2);
v___x_3598_ = lean_box(1);
v___x_3599_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0, &l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0);
v___x_3600_ = lean_box(0);
lean_inc_ref(v_env_3593_);
v___x_3601_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3599_, v_toEnvExtension_3596_, v_env_3593_, v_asyncMode_3597_, v___x_3600_);
v_importedEntries_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc_ref(v_importedEntries_3602_);
lean_dec(v___x_3601_);
v_extensions_3603_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3604_ = lean_array_size(v_importedEntries_3602_);
v___x_3605_ = ((size_t)0ULL);
lean_inc(v_tactic_3594_);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3594_, v_importedEntries_3602_, v_sz_3604_, v___x_3605_, v_extensions_3603_);
lean_dec_ref(v_importedEntries_3602_);
v___x_3607_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3598_, v___x_3595_, v_env_3593_, v_asyncMode_3597_, v___x_3600_);
v___x_3608_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3607_, v_tactic_3594_);
lean_dec(v_tactic_3594_);
lean_dec(v___x_3607_);
if (lean_obj_tag(v___x_3608_) == 1)
{
lean_object* v_val_3609_; lean_object* v___x_3610_; 
v_val_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_val_3609_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = l_Array_append___redArg(v___x_3606_, v_val_3609_);
lean_dec(v_val_3609_);
return v___x_3610_;
}
else
{
lean_dec(v___x_3608_);
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3611_, lean_object* v_k_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3611_, v_k_3612_, v_x_3613_, v_x_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3617_, lean_object* v_k_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3617_, v_k_3618_, v_x_3619_, v_x_3620_, v_x_3621_);
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_as_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3623_, lean_object* v_pos_3624_){
_start:
{
lean_object* v_str_3625_; lean_object* v_startInclusive_3626_; lean_object* v_endExclusive_3627_; lean_object* v___x_3628_; uint8_t v___y_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v_str_3625_ = lean_ctor_get(v_s_3623_, 0);
v_startInclusive_3626_ = lean_ctor_get(v_s_3623_, 1);
v_endExclusive_3627_ = lean_ctor_get(v_s_3623_, 2);
v___x_3628_ = lean_nat_add(v_startInclusive_3626_, v_pos_3624_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = lean_nat_sub(v_endExclusive_3627_, v___x_3628_);
v___x_3639_ = lean_nat_dec_eq(v___x_3637_, v___x_3638_);
lean_dec(v___x_3638_);
if (v___x_3639_ == 0)
{
uint32_t v___x_3640_; uint8_t v___y_3642_; uint32_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3640_ = lean_string_utf8_get_fast(v_str_3625_, v___x_3628_);
v___x_3647_ = 32;
v___x_3648_ = lean_uint32_dec_eq(v___x_3640_, v___x_3647_);
if (v___x_3648_ == 0)
{
uint32_t v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = 9;
v___x_3650_ = lean_uint32_dec_eq(v___x_3640_, v___x_3649_);
v___y_3642_ = v___x_3650_;
goto v___jp_3641_;
}
else
{
v___y_3642_ = v___x_3648_;
goto v___jp_3641_;
}
v___jp_3641_:
{
if (v___y_3642_ == 0)
{
uint32_t v___x_3643_; uint8_t v___x_3644_; 
v___x_3643_ = 13;
v___x_3644_ = lean_uint32_dec_eq(v___x_3640_, v___x_3643_);
if (v___x_3644_ == 0)
{
uint32_t v___x_3645_; uint8_t v___x_3646_; 
v___x_3645_ = 10;
v___x_3646_ = lean_uint32_dec_eq(v___x_3640_, v___x_3645_);
v___y_3636_ = v___x_3646_;
goto v___jp_3635_;
}
else
{
v___y_3636_ = v___x_3644_;
goto v___jp_3635_;
}
}
else
{
goto v___jp_3629_;
}
}
}
else
{
lean_dec(v___x_3628_);
return v_pos_3624_;
}
v___jp_3629_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3630_ = lean_string_utf8_next_fast(v_str_3625_, v___x_3628_);
v___x_3631_ = lean_nat_sub(v___x_3630_, v___x_3628_);
lean_dec(v___x_3628_);
v___x_3632_ = lean_nat_add(v_pos_3624_, v___x_3631_);
lean_dec(v___x_3631_);
v___x_3633_ = lean_nat_dec_lt(v_pos_3624_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_dec(v___x_3632_);
return v_pos_3624_;
}
else
{
lean_dec(v_pos_3624_);
v_pos_3624_ = v___x_3632_;
goto _start;
}
}
v___jp_3635_:
{
if (v___y_3636_ == 0)
{
lean_dec(v___x_3628_);
return v_pos_3624_;
}
else
{
goto v___jp_3629_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3651_, lean_object* v_pos_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3651_, v_pos_3652_);
lean_dec_ref(v_s_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3656_){
_start:
{
lean_object* v___y_3658_; lean_object* v_str_3661_; lean_object* v_startInclusive_3662_; lean_object* v_endExclusive_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_str_3661_ = lean_ctor_get(v_str_3656_, 0);
v_startInclusive_3662_ = lean_ctor_get(v_str_3656_, 1);
v_endExclusive_3663_ = lean_ctor_get(v_str_3656_, 2);
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3656_, v___x_3664_);
v___x_3666_ = lean_nat_sub(v_endExclusive_3663_, v_startInclusive_3662_);
v___x_3667_ = lean_nat_dec_eq(v___x_3665_, v___x_3666_);
lean_dec(v___x_3666_);
lean_dec(v___x_3665_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3669_ = lean_string_utf8_extract(v_str_3661_, v_startInclusive_3662_, v_endExclusive_3663_);
v___x_3670_ = lean_string_append(v___x_3668_, v___x_3669_);
lean_dec_ref(v___x_3669_);
v___y_3658_ = v___x_3670_;
goto v___jp_3657_;
}
else
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_string_utf8_extract(v_str_3661_, v_startInclusive_3662_, v_endExclusive_3663_);
v___y_3658_ = v___x_3671_;
goto v___jp_3657_;
}
v___jp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3660_ = lean_string_append(v___y_3658_, v___x_3659_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3672_);
lean_dec_ref(v_str_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0));
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3678_);
lean_dec_ref(v_s_3678_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3680_, lean_object* v___x_3681_, lean_object* v___x_3682_, lean_object* v_a_3683_, lean_object* v_b_3684_){
_start:
{
lean_object* v_it_3686_; lean_object* v_startInclusive_3687_; lean_object* v_endExclusive_3688_; 
if (lean_obj_tag(v_a_3683_) == 0)
{
lean_object* v_currPos_3692_; lean_object* v_searcher_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3719_; 
v_currPos_3692_ = lean_ctor_get(v_a_3683_, 0);
v_searcher_3693_ = lean_ctor_get(v_a_3683_, 1);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3695_ = v_a_3683_;
v_isShared_3696_ = v_isSharedCheck_3719_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_searcher_3693_);
lean_inc(v_currPos_3692_);
lean_dec(v_a_3683_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3719_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v_startInclusive_3697_; lean_object* v_endExclusive_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v_startInclusive_3697_ = lean_ctor_get(v___x_3681_, 1);
v_endExclusive_3698_ = lean_ctor_get(v___x_3681_, 2);
v___x_3699_ = lean_nat_sub(v_endExclusive_3698_, v_startInclusive_3697_);
v___x_3700_ = lean_nat_dec_eq(v_searcher_3693_, v___x_3699_);
lean_dec(v___x_3699_);
if (v___x_3700_ == 0)
{
uint32_t v___x_3701_; uint32_t v___x_3702_; uint8_t v___x_3703_; 
v___x_3701_ = 10;
v___x_3702_ = lean_string_utf8_get_fast(v_str_3680_, v_searcher_3693_);
v___x_3703_ = lean_uint32_dec_eq(v___x_3702_, v___x_3701_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_string_utf8_next_fast(v_str_3680_, v_searcher_3693_);
lean_dec(v_searcher_3693_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v___x_3704_);
v___x_3706_ = v___x_3695_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_currPos_3692_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
v_a_3683_ = v___x_3706_;
goto _start;
}
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v_slice_3712_; lean_object* v_nextIt_3714_; 
v___x_3709_ = lean_string_utf8_next_fast(v_str_3680_, v_searcher_3693_);
v___x_3710_ = lean_nat_sub(v___x_3709_, v_searcher_3693_);
v___x_3711_ = lean_nat_add(v_searcher_3693_, v___x_3710_);
lean_dec(v___x_3710_);
v_slice_3712_ = l_String_Slice_subslice_x21(v___x_3681_, v_currPos_3692_, v_searcher_3693_);
lean_inc(v___x_3711_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v___x_3711_);
lean_ctor_set(v___x_3695_, 0, v___x_3711_);
v_nextIt_3714_ = v___x_3695_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3711_);
v_nextIt_3714_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v_startInclusive_3715_; lean_object* v_endExclusive_3716_; 
v_startInclusive_3715_ = lean_ctor_get(v_slice_3712_, 0);
lean_inc(v_startInclusive_3715_);
v_endExclusive_3716_ = lean_ctor_get(v_slice_3712_, 1);
lean_inc(v_endExclusive_3716_);
lean_dec_ref(v_slice_3712_);
v_it_3686_ = v_nextIt_3714_;
v_startInclusive_3687_ = v_startInclusive_3715_;
v_endExclusive_3688_ = v_endExclusive_3716_;
goto v___jp_3685_;
}
}
}
else
{
lean_object* v___x_3718_; 
lean_del_object(v___x_3695_);
lean_dec(v_searcher_3693_);
v___x_3718_ = lean_box(1);
lean_inc(v___x_3682_);
v_it_3686_ = v___x_3718_;
v_startInclusive_3687_ = v_currPos_3692_;
v_endExclusive_3688_ = v___x_3682_;
goto v___jp_3685_;
}
}
}
else
{
lean_dec(v___x_3682_);
lean_dec_ref(v_str_3680_);
return v_b_3684_;
}
v___jp_3685_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_inc_ref(v_str_3680_);
v___x_3689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3689_, 0, v_str_3680_);
lean_ctor_set(v___x_3689_, 1, v_startInclusive_3687_);
lean_ctor_set(v___x_3689_, 2, v_endExclusive_3688_);
v___x_3690_ = lean_array_push(v_b_3684_, v___x_3689_);
v_a_3683_ = v_it_3686_;
v_b_3684_ = v___x_3690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3720_, lean_object* v___x_3721_, lean_object* v___x_3722_, lean_object* v_a_3723_, lean_object* v_b_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3720_, v___x_3721_, v___x_3722_, v_a_3723_, v_b_3724_);
lean_dec_ref(v___x_3721_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 0)
{
return v_x_3726_;
}
else
{
lean_object* v_head_3728_; lean_object* v_tail_3729_; lean_object* v___x_3730_; 
v_head_3728_ = lean_ctor_get(v_x_3727_, 0);
v_tail_3729_ = lean_ctor_get(v_x_3727_, 1);
v___x_3730_ = lean_string_append(v_x_3726_, v_head_3728_);
v_x_3726_ = v___x_3730_;
v_x_3727_ = v_tail_3729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3732_, lean_object* v_x_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3732_, v_x_3733_);
lean_dec(v_x_3733_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
if (lean_obj_tag(v_a_3735_) == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = l_List_reverse___redArg(v_a_3736_);
return v___x_3737_;
}
else
{
lean_object* v_head_3738_; lean_object* v_tail_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3748_; 
v_head_3738_ = lean_ctor_get(v_a_3735_, 0);
v_tail_3739_ = lean_ctor_get(v_a_3735_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3735_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3741_ = v_a_3735_;
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_tail_3739_);
lean_inc(v_head_3738_);
lean_dec(v_a_3735_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3743_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3738_);
lean_dec(v_head_3738_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v_a_3736_);
lean_ctor_set(v___x_3741_, 0, v___x_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_a_3736_);
v___x_3745_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
v_a_3735_ = v_tail_3739_;
v_a_3736_ = v___x_3745_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3753_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_lines_3760_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = lean_string_utf8_byte_size(v_str_3753_);
lean_inc_ref(v_str_3753_);
v___x_3756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3756_, 0, v_str_3753_);
lean_ctor_set(v___x_3756_, 1, v___x_3754_);
lean_ctor_set(v___x_3756_, 2, v___x_3755_);
v___x_3757_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v___x_3756_);
v___x_3758_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3759_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3753_, v___x_3756_, v___x_3755_, v___x_3757_, v___x_3758_);
lean_dec_ref(v___x_3756_);
v_lines_3760_ = lean_array_to_list(v___x_3759_);
if (lean_obj_tag(v_lines_3760_) == 0)
{
lean_object* v___x_3761_; 
v___x_3761_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3761_;
}
else
{
lean_object* v_tail_3762_; 
v_tail_3762_ = lean_ctor_get(v_lines_3760_, 1);
lean_inc(v_tail_3762_);
if (lean_obj_tag(v_tail_3762_) == 0)
{
lean_object* v_head_3763_; lean_object* v_str_3764_; lean_object* v_startInclusive_3765_; lean_object* v_endExclusive_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_head_3763_ = lean_ctor_get(v_lines_3760_, 0);
lean_inc(v_head_3763_);
lean_dec_ref(v_lines_3760_);
v_str_3764_ = lean_ctor_get(v_head_3763_, 0);
lean_inc_ref(v_str_3764_);
v_startInclusive_3765_ = lean_ctor_get(v_head_3763_, 1);
lean_inc(v_startInclusive_3765_);
v_endExclusive_3766_ = lean_ctor_get(v_head_3763_, 2);
lean_inc(v_endExclusive_3766_);
lean_dec(v_head_3763_);
v___x_3767_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3768_ = lean_string_utf8_extract(v_str_3764_, v_startInclusive_3765_, v_endExclusive_3766_);
lean_dec(v_endExclusive_3766_);
lean_dec(v_startInclusive_3765_);
lean_dec_ref(v_str_3764_);
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
return v___x_3771_;
}
else
{
lean_object* v_head_3772_; lean_object* v_str_3773_; lean_object* v_startInclusive_3774_; lean_object* v_endExclusive_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_head_3772_ = lean_ctor_get(v_lines_3760_, 0);
lean_inc(v_head_3772_);
lean_dec_ref(v_lines_3760_);
v_str_3773_ = lean_ctor_get(v_head_3772_, 0);
lean_inc_ref(v_str_3773_);
v_startInclusive_3774_ = lean_ctor_get(v_head_3772_, 1);
lean_inc(v_startInclusive_3774_);
v_endExclusive_3775_ = lean_ctor_get(v_head_3772_, 2);
lean_inc(v_endExclusive_3775_);
lean_dec(v_head_3772_);
v___x_3776_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3777_ = lean_string_utf8_extract(v_str_3773_, v_startInclusive_3774_, v_endExclusive_3775_);
lean_dec(v_endExclusive_3775_);
lean_dec(v_startInclusive_3774_);
lean_dec_ref(v_str_3773_);
v___x_3778_ = lean_string_append(v___x_3776_, v___x_3777_);
lean_dec_ref(v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
v___x_3781_ = lean_box(0);
v___x_3782_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3762_, v___x_3781_);
v___x_3783_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3784_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3783_, v___x_3782_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_string_append(v___x_3780_, v___x_3784_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3787_ = lean_string_append(v___x_3785_, v___x_3786_);
return v___x_3787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3788_, lean_object* v___x_3789_, lean_object* v___x_3790_, lean_object* v_inst_3791_, lean_object* v_R_3792_, lean_object* v_a_3793_, lean_object* v_b_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3788_, v___x_3789_, v___x_3790_, v_a_3793_, v_b_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3796_, lean_object* v___x_3797_, lean_object* v___x_3798_, lean_object* v_inst_3799_, lean_object* v_R_3800_, lean_object* v_a_3801_, lean_object* v_b_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3796_, v___x_3797_, v___x_3798_, v_inst_3799_, v_R_3800_, v_a_3801_, v_b_3802_);
lean_dec_ref(v___x_3797_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
if (lean_obj_tag(v_a_3804_) == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = l_List_reverse___redArg(v_a_3805_);
return v___x_3806_;
}
else
{
lean_object* v_head_3807_; lean_object* v_tail_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3817_; 
v_head_3807_ = lean_ctor_get(v_a_3804_, 0);
v_tail_3808_ = lean_ctor_get(v_a_3804_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_a_3804_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3810_ = v_a_3804_;
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_tail_3808_);
lean_inc(v_head_3807_);
lean_dec(v_a_3804_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3812_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3807_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 1, v_a_3805_);
lean_ctor_set(v___x_3810_, 0, v___x_3812_);
v___x_3814_ = v___x_3810_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_a_3805_);
v___x_3814_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
v_a_3804_ = v_tail_3808_;
v_a_3805_ = v___x_3814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3818_, lean_object* v_pos_3819_){
_start:
{
lean_object* v_str_3820_; lean_object* v_startInclusive_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_str_3820_ = lean_ctor_get(v_s_3818_, 0);
v_startInclusive_3821_ = lean_ctor_get(v_s_3818_, 1);
v___x_3822_ = lean_nat_add(v_startInclusive_3821_, v_pos_3819_);
v___x_3823_ = lean_nat_sub(v___x_3822_, v_startInclusive_3821_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_nat_dec_eq(v___x_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___y_3834_; lean_object* v___x_3835_; uint32_t v___x_3836_; uint8_t v___y_3838_; uint32_t v___x_3843_; uint8_t v___x_3844_; 
lean_inc(v_startInclusive_3821_);
lean_inc_ref(v_str_3820_);
v___x_3826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3826_, 0, v_str_3820_);
lean_ctor_set(v___x_3826_, 1, v_startInclusive_3821_);
lean_ctor_set(v___x_3826_, 2, v___x_3822_);
v___x_3827_ = lean_unsigned_to_nat(1u);
v___x_3828_ = lean_nat_sub(v___x_3823_, v___x_3827_);
lean_dec(v___x_3823_);
v___x_3829_ = l_String_Slice_posLE(v___x_3826_, v___x_3828_);
lean_dec_ref(v___x_3826_);
v___x_3835_ = lean_nat_add(v_startInclusive_3821_, v___x_3829_);
v___x_3836_ = lean_string_utf8_get_fast(v_str_3820_, v___x_3835_);
lean_dec(v___x_3835_);
v___x_3843_ = 32;
v___x_3844_ = lean_uint32_dec_eq(v___x_3836_, v___x_3843_);
if (v___x_3844_ == 0)
{
uint32_t v___x_3845_; uint8_t v___x_3846_; 
v___x_3845_ = 9;
v___x_3846_ = lean_uint32_dec_eq(v___x_3836_, v___x_3845_);
v___y_3838_ = v___x_3846_;
goto v___jp_3837_;
}
else
{
v___y_3838_ = v___x_3844_;
goto v___jp_3837_;
}
v___jp_3830_:
{
uint8_t v___x_3831_; 
v___x_3831_ = lean_nat_dec_lt(v___x_3829_, v_pos_3819_);
if (v___x_3831_ == 0)
{
lean_dec(v___x_3829_);
return v_pos_3819_;
}
else
{
lean_dec(v_pos_3819_);
v_pos_3819_ = v___x_3829_;
goto _start;
}
}
v___jp_3833_:
{
if (v___y_3834_ == 0)
{
lean_dec(v___x_3829_);
return v_pos_3819_;
}
else
{
goto v___jp_3830_;
}
}
v___jp_3837_:
{
if (v___y_3838_ == 0)
{
uint32_t v___x_3839_; uint8_t v___x_3840_; 
v___x_3839_ = 13;
v___x_3840_ = lean_uint32_dec_eq(v___x_3836_, v___x_3839_);
if (v___x_3840_ == 0)
{
uint32_t v___x_3841_; uint8_t v___x_3842_; 
v___x_3841_ = 10;
v___x_3842_ = lean_uint32_dec_eq(v___x_3836_, v___x_3841_);
v___y_3834_ = v___x_3842_;
goto v___jp_3833_;
}
else
{
v___y_3834_ = v___x_3840_;
goto v___jp_3833_;
}
}
else
{
goto v___jp_3830_;
}
}
}
else
{
lean_dec(v___x_3823_);
lean_dec(v___x_3822_);
return v_pos_3819_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3847_, lean_object* v_pos_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3847_, v_pos_3848_);
lean_dec_ref(v_s_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3851_, lean_object* v_tactic_3852_){
_start:
{
lean_object* v_exts_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_exts_3853_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3851_, v_tactic_3852_);
v___x_3854_ = lean_array_get_size(v_exts_3853_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_nat_dec_eq(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3857_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3858_ = lean_array_to_list(v_exts_3853_);
v___x_3859_ = lean_box(0);
v___x_3860_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3858_, v___x_3859_);
v___x_3861_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3862_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3861_, v___x_3860_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_string_append(v___x_3857_, v___x_3862_);
lean_dec_ref(v___x_3862_);
v___x_3864_ = lean_string_utf8_byte_size(v___x_3863_);
lean_inc_ref(v___x_3863_);
v___x_3865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3855_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
v___x_3866_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3865_, v___x_3864_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = lean_string_utf8_extract(v___x_3863_, v___x_3855_, v___x_3866_);
lean_dec(v___x_3866_);
lean_dec_ref(v___x_3863_);
return v___x_3867_;
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_exts_3853_);
v___x_3868_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3869_, lean_object* v_x_3870_){
_start:
{
lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___x_3873_; 
v_fst_3871_ = lean_ctor_get(v_x_3870_, 0);
lean_inc(v_fst_3871_);
v_snd_3872_ = lean_ctor_get(v_x_3870_, 1);
lean_inc(v_snd_3872_);
lean_dec_ref(v_x_3870_);
v___x_3873_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3871_, v_snd_3872_, v_as_3869_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3874_, lean_object* v_x_3875_){
_start:
{
if (lean_obj_tag(v_x_3875_) == 0)
{
lean_object* v_k_3876_; lean_object* v_v_3877_; lean_object* v_l_3878_; lean_object* v_r_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_k_3876_ = lean_ctor_get(v_x_3875_, 1);
v_v_3877_ = lean_ctor_get(v_x_3875_, 2);
v_l_3878_ = lean_ctor_get(v_x_3875_, 3);
v_r_3879_ = lean_ctor_get(v_x_3875_, 4);
v___x_3880_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3874_, v_l_3878_);
lean_inc(v_v_3877_);
lean_inc(v_k_3876_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_k_3876_);
lean_ctor_set(v___x_3881_, 1, v_v_3877_);
v___x_3882_ = lean_array_push(v___x_3880_, v___x_3881_);
v_init_3874_ = v___x_3882_;
v_x_3875_ = v_r_3879_;
goto _start;
}
else
{
return v_init_3874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3884_, lean_object* v_x_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3884_, v_x_3885_);
lean_dec(v_x_3885_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_3887_, lean_object* v_pivot_3888_, lean_object* v_as_3889_, lean_object* v_i_3890_, lean_object* v_k_3891_){
_start:
{
uint8_t v___x_3892_; 
v___x_3892_ = lean_nat_dec_lt(v_k_3891_, v_hi_3887_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_dec(v_k_3891_);
v___x_3893_ = lean_array_fswap(v_as_3889_, v_i_3890_, v_hi_3887_);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_i_3890_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
return v___x_3894_;
}
else
{
lean_object* v___x_3895_; lean_object* v_fst_3896_; lean_object* v_fst_3897_; uint8_t v___x_3898_; 
v___x_3895_ = lean_array_fget_borrowed(v_as_3889_, v_k_3891_);
v_fst_3896_ = lean_ctor_get(v___x_3895_, 0);
v_fst_3897_ = lean_ctor_get(v_pivot_3888_, 0);
v___x_3898_ = l_Lean_Name_quickLt(v_fst_3896_, v_fst_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_add(v_k_3891_, v___x_3899_);
lean_dec(v_k_3891_);
v_k_3891_ = v___x_3900_;
goto _start;
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3902_ = lean_array_fswap(v_as_3889_, v_i_3890_, v_k_3891_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_add(v_i_3890_, v___x_3903_);
lean_dec(v_i_3890_);
v___x_3905_ = lean_nat_add(v_k_3891_, v___x_3903_);
lean_dec(v_k_3891_);
v_as_3889_ = v___x_3902_;
v_i_3890_ = v___x_3904_;
v_k_3891_ = v___x_3905_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_3907_, lean_object* v_pivot_3908_, lean_object* v_as_3909_, lean_object* v_i_3910_, lean_object* v_k_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3907_, v_pivot_3908_, v_as_3909_, v_i_3910_, v_k_3911_);
lean_dec_ref(v_pivot_3908_);
lean_dec(v_hi_3907_);
return v_res_3912_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3913_, lean_object* v_x2_3914_){
_start:
{
lean_object* v_fst_3915_; lean_object* v_fst_3916_; uint8_t v___x_3917_; 
v_fst_3915_ = lean_ctor_get(v_x1_3913_, 0);
v_fst_3916_ = lean_ctor_get(v_x2_3914_, 0);
v___x_3917_ = l_Lean_Name_quickLt(v_fst_3915_, v_fst_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3918_, lean_object* v_x2_3919_){
_start:
{
uint8_t v_res_3920_; lean_object* v_r_3921_; 
v_res_3920_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3918_, v_x2_3919_);
lean_dec_ref(v_x2_3919_);
lean_dec_ref(v_x1_3918_);
v_r_3921_ = lean_box(v_res_3920_);
return v_r_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_3922_, lean_object* v_as_3923_, lean_object* v_lo_3924_, lean_object* v_hi_3925_){
_start:
{
lean_object* v___y_3927_; uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_lt(v_lo_3924_, v_hi_3925_);
if (v___x_3937_ == 0)
{
lean_dec(v_lo_3924_);
return v_as_3923_;
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v_mid_3940_; lean_object* v___y_3942_; lean_object* v___y_3948_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3938_ = lean_nat_add(v_lo_3924_, v_hi_3925_);
v___x_3939_ = lean_unsigned_to_nat(1u);
v_mid_3940_ = lean_nat_shiftr(v___x_3938_, v___x_3939_);
lean_dec(v___x_3938_);
v___x_3953_ = lean_array_fget_borrowed(v_as_3923_, v_mid_3940_);
v___x_3954_ = lean_array_fget_borrowed(v_as_3923_, v_lo_3924_);
v___x_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
v___y_3948_ = v_as_3923_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_array_fswap(v_as_3923_, v_lo_3924_, v_mid_3940_);
v___y_3948_ = v___x_3956_;
goto v___jp_3947_;
}
v___jp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3943_ = lean_array_fget_borrowed(v___y_3942_, v_mid_3940_);
v___x_3944_ = lean_array_fget_borrowed(v___y_3942_, v_hi_3925_);
v___x_3945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3943_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec(v_mid_3940_);
v___y_3927_ = v___y_3942_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3946_; 
v___x_3946_ = lean_array_fswap(v___y_3942_, v_mid_3940_, v_hi_3925_);
lean_dec(v_mid_3940_);
v___y_3927_ = v___x_3946_;
goto v___jp_3926_;
}
}
v___jp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = lean_array_fget_borrowed(v___y_3948_, v_hi_3925_);
v___x_3950_ = lean_array_fget_borrowed(v___y_3948_, v_lo_3924_);
v___x_3951_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
v___y_3942_ = v___y_3948_;
goto v___jp_3941_;
}
else
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_array_fswap(v___y_3948_, v_lo_3924_, v_hi_3925_);
v___y_3942_ = v___x_3952_;
goto v___jp_3941_;
}
}
}
v___jp_3926_:
{
lean_object* v_pivot_3928_; lean_object* v___x_3929_; lean_object* v_fst_3930_; lean_object* v_snd_3931_; uint8_t v___x_3932_; 
v_pivot_3928_ = lean_array_fget(v___y_3927_, v_hi_3925_);
lean_inc_n(v_lo_3924_, 2);
v___x_3929_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_3925_, v_pivot_3928_, v___y_3927_, v_lo_3924_, v_lo_3924_);
lean_dec(v_pivot_3928_);
v_fst_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_fst_3930_);
v_snd_3931_ = lean_ctor_get(v___x_3929_, 1);
lean_inc(v_snd_3931_);
lean_dec_ref(v___x_3929_);
v___x_3932_ = lean_nat_dec_le(v_hi_3925_, v_fst_3930_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3933_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3922_, v_snd_3931_, v_lo_3924_, v_fst_3930_);
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = lean_nat_add(v_fst_3930_, v___x_3934_);
lean_dec(v_fst_3930_);
v_as_3923_ = v___x_3933_;
v_lo_3924_ = v___x_3935_;
goto _start;
}
else
{
lean_dec(v_fst_3930_);
lean_dec(v_lo_3924_);
return v_snd_3931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_3957_, lean_object* v_as_3958_, lean_object* v_lo_3959_, lean_object* v_hi_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_3957_, v_as_3958_, v_lo_3959_, v_hi_3960_);
lean_dec(v_hi_3960_);
lean_dec(v_n_3957_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3964_, lean_object* v_s_3965_){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___x_3975_; 
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3968_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3967_, v_s_3965_);
v___x_3969_ = lean_array_get_size(v___x_3968_);
v___x_3975_ = lean_nat_dec_eq(v___x_3969_, v___x_3966_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___y_3979_; uint8_t v___x_3981_; 
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_sub(v___x_3969_, v___x_3976_);
v___x_3981_ = lean_nat_dec_le(v___x_3966_, v___x_3977_);
if (v___x_3981_ == 0)
{
lean_inc(v___x_3977_);
v___y_3979_ = v___x_3977_;
goto v___jp_3978_;
}
else
{
v___y_3979_ = v___x_3966_;
goto v___jp_3978_;
}
v___jp_3978_:
{
uint8_t v___x_3980_; 
v___x_3980_ = lean_nat_dec_le(v___y_3979_, v___x_3977_);
if (v___x_3980_ == 0)
{
lean_dec(v___x_3977_);
lean_inc(v___y_3979_);
v___y_3971_ = v___y_3979_;
v___y_3972_ = v___y_3979_;
goto v___jp_3970_;
}
else
{
v___y_3971_ = v___y_3979_;
v___y_3972_ = v___x_3977_;
goto v___jp_3970_;
}
}
}
else
{
lean_object* v___x_3982_; 
lean_inc_ref_n(v___x_3968_, 2);
v___x_3982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3968_);
lean_ctor_set(v___x_3982_, 1, v___x_3968_);
lean_ctor_set(v___x_3982_, 2, v___x_3968_);
return v___x_3982_;
}
v___jp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3969_, v___x_3968_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_inc_ref_n(v___x_3973_, 2);
v___x_3974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
lean_ctor_set(v___x_3974_, 2, v___x_3973_);
return v___x_3974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3983_, lean_object* v_s_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3983_, v_s_3984_);
lean_dec(v_s_3984_);
lean_dec_ref(v_x_3983_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3986_){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3988_, v_es_3986_);
v___x_3990_ = lean_array_get_size(v___x_3989_);
v___x_3991_ = lean_nat_dec_eq(v___x_3990_, v___x_3987_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___y_3995_; uint8_t v___x_3999_; 
v___x_3992_ = lean_unsigned_to_nat(1u);
v___x_3993_ = lean_nat_sub(v___x_3990_, v___x_3992_);
v___x_3999_ = lean_nat_dec_le(v___x_3987_, v___x_3993_);
if (v___x_3999_ == 0)
{
lean_inc(v___x_3993_);
v___y_3995_ = v___x_3993_;
goto v___jp_3994_;
}
else
{
v___y_3995_ = v___x_3987_;
goto v___jp_3994_;
}
v___jp_3994_:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_nat_dec_le(v___y_3995_, v___x_3993_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
lean_dec(v___x_3993_);
lean_inc(v___y_3995_);
v___x_3997_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3990_, v___x_3989_, v___y_3995_, v___y_3995_);
lean_dec(v___y_3995_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; 
v___x_3998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3990_, v___x_3989_, v___y_3995_, v___x_3993_);
lean_dec(v___x_3993_);
return v___x_3998_;
}
}
}
else
{
return v___x_3989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_4000_);
lean_dec(v_es_4000_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_4002_, lean_object* v_x_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4002_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_4007_, lean_object* v_x_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_4007_, v_x_4008_, v___y_4009_);
lean_dec_ref(v___y_4009_);
lean_dec_ref(v_x_4008_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_4038_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_4041_, lean_object* v_t_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_4041_, v_t_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_4044_, lean_object* v_t_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_4044_, v_t_4045_);
lean_dec(v_t_4045_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_4047_, lean_object* v_as_4048_, lean_object* v_lo_4049_, lean_object* v_hi_4050_, lean_object* v_w_4051_, lean_object* v_hlo_4052_, lean_object* v_hhi_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_n_4047_, v_as_4048_, v_lo_4049_, v_hi_4050_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_4055_, lean_object* v_as_4056_, lean_object* v_lo_4057_, lean_object* v_hi_4058_, lean_object* v_w_4059_, lean_object* v_hlo_4060_, lean_object* v_hhi_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_4055_, v_as_4056_, v_lo_4057_, v_hi_4058_, v_w_4059_, v_hlo_4060_, v_hhi_4061_);
lean_dec(v_hi_4058_);
lean_dec(v_n_4055_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_4063_, lean_object* v_lo_4064_, lean_object* v_hi_4065_, lean_object* v_hhi_4066_, lean_object* v_pivot_4067_, lean_object* v_as_4068_, lean_object* v_i_4069_, lean_object* v_k_4070_, lean_object* v_ilo_4071_, lean_object* v_ik_4072_, lean_object* v_w_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_4065_, v_pivot_4067_, v_as_4068_, v_i_4069_, v_k_4070_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_4075_, lean_object* v_lo_4076_, lean_object* v_hi_4077_, lean_object* v_hhi_4078_, lean_object* v_pivot_4079_, lean_object* v_as_4080_, lean_object* v_i_4081_, lean_object* v_k_4082_, lean_object* v_ilo_4083_, lean_object* v_ik_4084_, lean_object* v_w_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1_spec__2(v_n_4075_, v_lo_4076_, v_hi_4077_, v_hhi_4078_, v_pivot_4079_, v_as_4080_, v_i_4081_, v_k_4082_, v_ilo_4083_, v_ik_4084_, v_w_4085_);
lean_dec_ref(v_pivot_4079_);
lean_dec(v_hi_4077_);
lean_dec(v_lo_4076_);
lean_dec(v_n_4075_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_4088_, lean_object* v___x_4089_, lean_object* v_toPure_4090_, lean_object* v___f_4091_, lean_object* v_env_4092_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4092_, v_tac_4088_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; lean_object* v_toEnvExtension_4098_; lean_object* v_asyncMode_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref(v___f_4091_);
v___x_4097_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4098_ = lean_ctor_get(v___x_4097_, 0);
v_asyncMode_4099_ = lean_ctor_get(v_toEnvExtension_4098_, 2);
v___x_4100_ = lean_box(0);
v___x_4101_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4089_, v___x_4097_, v_env_4092_, v_asyncMode_4099_, v___x_4100_);
v___x_4102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4101_, v_tac_4088_);
lean_dec(v_tac_4088_);
lean_dec(v___x_4101_);
v___x_4103_ = lean_apply_2(v_toPure_4090_, lean_box(0), v___x_4102_);
return v___x_4103_;
}
else
{
lean_object* v_val_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v_val_4104_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_val_4104_);
lean_dec_ref(v___x_4096_);
v___x_4105_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4106_ = 0;
v___x_4107_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4089_, v___x_4105_, v_env_4092_, v_val_4104_, v___x_4106_);
lean_dec(v_val_4104_);
lean_dec_ref(v_env_4092_);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_array_get_size(v___x_4107_);
v___x_4110_ = lean_nat_dec_lt(v___x_4108_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___f_4091_);
lean_dec(v_tac_4088_);
goto v___jp_4093_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4111_ = lean_unsigned_to_nat(1u);
v___x_4112_ = lean_nat_sub(v___x_4109_, v___x_4111_);
v___x_4113_ = lean_nat_dec_le(v___x_4108_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_dec(v___x_4112_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___f_4091_);
lean_dec(v_tac_4088_);
goto v___jp_4093_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4114_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_tac_4088_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_4117_ = l_Array_binSearchAux___redArg(v___f_4091_, v___x_4116_, v___x_4107_, v___x_4115_, v___x_4108_, v___x_4112_);
lean_dec_ref(v___x_4107_);
if (lean_obj_tag(v___x_4117_) == 0)
{
goto v___jp_4093_;
}
else
{
lean_object* v_val_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4127_; 
v_val_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_val_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v_snd_4122_; lean_object* v___x_4124_; 
v_snd_4122_ = lean_ctor_get(v_val_4118_, 1);
lean_inc(v_snd_4122_);
lean_dec(v_val_4118_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_snd_4122_);
v___x_4124_ = v___x_4120_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_snd_4122_);
v___x_4124_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_apply_2(v_toPure_4090_, lean_box(0), v___x_4124_);
return v___x_4125_;
}
}
}
}
}
}
v___jp_4093_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_box(0);
v___x_4095_ = lean_apply_2(v_toPure_4090_, lean_box(0), v___x_4094_);
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_4129_, lean_object* v_inst_4130_, lean_object* v_tac_4131_){
_start:
{
lean_object* v_toApplicative_4132_; lean_object* v_toBind_4133_; lean_object* v_getEnv_4134_; lean_object* v_toPure_4135_; lean_object* v___f_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; 
v_toApplicative_4132_ = lean_ctor_get(v_inst_4129_, 0);
lean_inc_ref(v_toApplicative_4132_);
v_toBind_4133_ = lean_ctor_get(v_inst_4129_, 1);
lean_inc(v_toBind_4133_);
lean_dec_ref(v_inst_4129_);
v_getEnv_4134_ = lean_ctor_get(v_inst_4130_, 0);
lean_inc(v_getEnv_4134_);
lean_dec_ref(v_inst_4130_);
v_toPure_4135_ = lean_ctor_get(v_toApplicative_4132_, 1);
lean_inc(v_toPure_4135_);
lean_dec_ref(v_toApplicative_4132_);
v___f_4136_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___closed__0));
v___x_4137_ = lean_box(1);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4138_, 0, v_tac_4131_);
lean_closure_set(v___f_4138_, 1, v___x_4137_);
lean_closure_set(v___f_4138_, 2, v_toPure_4135_);
lean_closure_set(v___f_4138_, 3, v___f_4136_);
v___x_4139_ = lean_apply_4(v_toBind_4133_, lean_box(0), lean_box(0), v_getEnv_4134_, v___f_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_tac_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_4141_, v_inst_4142_, v_tac_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4145_, lean_object* v_k_4146_, lean_object* v_x_4147_, lean_object* v_x_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v_m_4151_; lean_object* v_a_4152_; uint8_t v___x_4153_; 
v___x_4149_ = lean_nat_add(v_x_4147_, v_x_4148_);
v___x_4150_ = lean_unsigned_to_nat(1u);
v_m_4151_ = lean_nat_shiftr(v___x_4149_, v___x_4150_);
lean_dec(v___x_4149_);
v_a_4152_ = lean_array_fget_borrowed(v_as_4145_, v_m_4151_);
v___x_4153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_4152_, v_k_4146_);
if (v___x_4153_ == 0)
{
uint8_t v___x_4154_; 
lean_dec(v_x_4148_);
v___x_4154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_4146_, v_a_4152_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
lean_dec(v_m_4151_);
lean_dec(v_x_4147_);
lean_inc(v_a_4152_);
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_a_4152_);
return v___x_4155_;
}
else
{
lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = lean_nat_dec_eq(v_m_4151_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; uint8_t v___x_4159_; 
v___x_4158_ = lean_nat_sub(v_m_4151_, v___x_4150_);
lean_dec(v_m_4151_);
v___x_4159_ = lean_nat_dec_lt(v___x_4158_, v_x_4147_);
if (v___x_4159_ == 0)
{
v_x_4148_ = v___x_4158_;
goto _start;
}
else
{
lean_object* v___x_4161_; 
lean_dec(v___x_4158_);
lean_dec(v_x_4147_);
v___x_4161_ = lean_box(0);
return v___x_4161_;
}
}
else
{
lean_object* v___x_4162_; 
lean_dec(v_m_4151_);
lean_dec(v_x_4147_);
v___x_4162_ = lean_box(0);
return v___x_4162_;
}
}
}
else
{
lean_object* v___x_4163_; uint8_t v___x_4164_; 
lean_dec(v_x_4147_);
v___x_4163_ = lean_nat_add(v_m_4151_, v___x_4150_);
lean_dec(v_m_4151_);
v___x_4164_ = lean_nat_dec_le(v___x_4163_, v_x_4148_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; 
lean_dec(v___x_4163_);
lean_dec(v_x_4148_);
v___x_4165_ = lean_box(0);
return v___x_4165_;
}
else
{
v_x_4147_ = v___x_4163_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4167_, lean_object* v_k_4168_, lean_object* v_x_4169_, lean_object* v_x_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4167_, v_k_4168_, v_x_4169_, v_x_4170_);
lean_dec_ref(v_k_4168_);
lean_dec_ref(v_as_4167_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; lean_object* v_env_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4175_ = lean_st_ref_get(v___y_4173_);
v_env_4179_ = lean_ctor_get(v___x_4175_, 0);
lean_inc_ref(v_env_4179_);
lean_dec(v___x_4175_);
v___x_4180_ = lean_box(1);
v___x_4181_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4179_, v_tac_4172_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v___x_4182_; lean_object* v_toEnvExtension_4183_; lean_object* v_asyncMode_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4182_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4183_ = lean_ctor_get(v___x_4182_, 0);
v_asyncMode_4184_ = lean_ctor_get(v_toEnvExtension_4183_, 2);
v___x_4185_ = lean_box(0);
v___x_4186_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4180_, v___x_4182_, v_env_4179_, v_asyncMode_4184_, v___x_4185_);
v___x_4187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4186_, v_tac_4172_);
lean_dec(v_tac_4172_);
lean_dec(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
else
{
lean_object* v_val_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4217_; 
v_val_4189_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4191_ = v___x_4181_;
v_isShared_4192_ = v_isSharedCheck_4217_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_val_4189_);
lean_dec(v___x_4181_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4217_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4193_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_4194_ = 0;
v___x_4195_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4180_, v___x_4193_, v_env_4179_, v_val_4189_, v___x_4194_);
lean_dec(v_val_4189_);
lean_dec_ref(v_env_4179_);
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_array_get_size(v___x_4195_);
v___x_4198_ = lean_nat_dec_lt(v___x_4196_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_dec_ref(v___x_4195_);
lean_del_object(v___x_4191_);
lean_dec(v_tac_4172_);
goto v___jp_4176_;
}
else
{
lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_nat_sub(v___x_4197_, v___x_4199_);
v___x_4201_ = lean_nat_dec_le(v___x_4196_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_dec(v___x_4200_);
lean_dec_ref(v___x_4195_);
lean_del_object(v___x_4191_);
lean_dec(v_tac_4172_);
goto v___jp_4176_;
}
else
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v_tac_4172_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_4195_, v___x_4203_, v___x_4196_, v___x_4200_);
lean_dec_ref(v___x_4203_);
lean_dec_ref(v___x_4195_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_del_object(v___x_4191_);
goto v___jp_4176_;
}
else
{
lean_object* v_val_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4216_; 
v_val_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4216_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_val_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4216_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v_snd_4209_; lean_object* v___x_4211_; 
v_snd_4209_ = lean_ctor_get(v_val_4205_, 1);
lean_inc(v_snd_4209_);
lean_dec(v_val_4205_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_snd_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_snd_4209_);
v___x_4211_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4192_ == 0)
{
lean_ctor_set_tag(v___x_4191_, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4211_);
v___x_4213_ = v___x_4191_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
}
}
v___jp_4176_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4218_, v___y_4219_);
lean_dec(v___y_4219_);
return v_res_4221_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4224_ = l_Lean_stringToMessageData(v___x_4223_);
return v___x_4224_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4227_ = l_Lean_stringToMessageData(v___x_4226_);
return v___x_4227_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4233_ = l_Lean_stringToMessageData(v___x_4232_);
return v___x_4233_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4236_ = l_Lean_stringToMessageData(v___x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_4243_, lean_object* v___x_4244_, lean_object* v___x_4245_, lean_object* v___x_4246_, lean_object* v_name_4247_, lean_object* v_decl_4248_, lean_object* v_stx_4249_, uint8_t v_kind_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; uint8_t v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v_name_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; uint8_t v___x_4408_; uint8_t v___x_4409_; 
v___x_4408_ = 0;
v___x_4409_ = l_Lean_instBEqAttributeKind_beq(v_kind_4250_, v___x_4408_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; 
lean_dec(v_stx_4249_);
lean_dec(v_decl_4248_);
lean_dec_ref(v___x_4246_);
lean_dec_ref(v___x_4245_);
lean_dec_ref(v___x_4244_);
lean_dec(v___x_4243_);
v___x_4410_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_4247_, v_kind_4250_, v___y_4251_, v___y_4252_);
return v___x_4410_;
}
else
{
goto v___jp_4367_;
}
v___jp_4254_:
{
lean_object* v___x_4257_; lean_object* v_env_4258_; lean_object* v_nextMacroScope_4259_; lean_object* v_ngen_4260_; lean_object* v_auxDeclNGen_4261_; lean_object* v_traceState_4262_; lean_object* v_messages_4263_; lean_object* v_infoState_4264_; lean_object* v_snapshotTasks_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4281_; 
v___x_4257_ = lean_st_ref_take(v___y_4256_);
v_env_4258_ = lean_ctor_get(v___x_4257_, 0);
v_nextMacroScope_4259_ = lean_ctor_get(v___x_4257_, 1);
v_ngen_4260_ = lean_ctor_get(v___x_4257_, 2);
v_auxDeclNGen_4261_ = lean_ctor_get(v___x_4257_, 3);
v_traceState_4262_ = lean_ctor_get(v___x_4257_, 4);
v_messages_4263_ = lean_ctor_get(v___x_4257_, 6);
v_infoState_4264_ = lean_ctor_get(v___x_4257_, 7);
v_snapshotTasks_4265_ = lean_ctor_get(v___x_4257_, 8);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4281_ == 0)
{
lean_object* v_unused_4282_; 
v_unused_4282_ = lean_ctor_get(v___x_4257_, 5);
lean_dec(v_unused_4282_);
v___x_4267_ = v___x_4257_;
v_isShared_4268_ = v_isSharedCheck_4281_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_snapshotTasks_4265_);
lean_inc(v_infoState_4264_);
lean_inc(v_messages_4263_);
lean_inc(v_traceState_4262_);
lean_inc(v_auxDeclNGen_4261_);
lean_inc(v_ngen_4260_);
lean_inc(v_nextMacroScope_4259_);
lean_inc(v_env_4258_);
lean_dec(v___x_4257_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4281_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4269_; lean_object* v_toEnvExtension_4270_; lean_object* v_asyncMode_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4269_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4270_ = lean_ctor_get(v___x_4269_, 0);
v_asyncMode_4271_ = lean_ctor_get(v_toEnvExtension_4270_, 2);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v_decl_4248_);
lean_ctor_set(v___x_4272_, 1, v___y_4255_);
v___x_4273_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4269_, v_env_4258_, v___x_4272_, v_asyncMode_4271_, v___x_4243_);
v___x_4274_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 5, v___x_4274_);
lean_ctor_set(v___x_4267_, 0, v___x_4273_);
v___x_4276_ = v___x_4267_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_nextMacroScope_4259_);
lean_ctor_set(v_reuseFailAlloc_4280_, 2, v_ngen_4260_);
lean_ctor_set(v_reuseFailAlloc_4280_, 3, v_auxDeclNGen_4261_);
lean_ctor_set(v_reuseFailAlloc_4280_, 4, v_traceState_4262_);
lean_ctor_set(v_reuseFailAlloc_4280_, 5, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4280_, 6, v_messages_4263_);
lean_ctor_set(v_reuseFailAlloc_4280_, 7, v_infoState_4264_);
lean_ctor_set(v_reuseFailAlloc_4280_, 8, v_snapshotTasks_4265_);
v___x_4276_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4277_ = lean_st_ref_set(v___y_4256_, v___x_4276_);
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
return v___x_4279_;
}
}
}
v___jp_4283_:
{
lean_object* v___x_4287_; lean_object* v_a_4288_; 
lean_inc(v_decl_4248_);
v___x_4287_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_4248_, v___y_4286_);
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___x_4287_);
if (lean_obj_tag(v_a_4288_) == 1)
{
lean_object* v_val_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_dec_ref(v___y_4284_);
lean_dec(v___x_4243_);
v_val_4289_ = lean_ctor_get(v_a_4288_, 0);
lean_inc(v_val_4289_);
lean_dec_ref(v_a_4288_);
v___x_4290_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4291_ = 0;
v___x_4292_ = l_Lean_MessageData_ofConstName(v_decl_4248_, v___x_4291_);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4290_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = l_Lean_stringToMessageData(v_val_4289_);
v___x_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4299_, v___y_4285_, v___y_4286_);
return v___x_4300_;
}
else
{
lean_dec(v_a_4288_);
v___y_4255_ = v___y_4284_;
v___y_4256_ = v___y_4286_;
goto v___jp_4254_;
}
}
v___jp_4301_:
{
lean_object* v___x_4305_; lean_object* v_env_4306_; lean_object* v___x_4307_; 
v___x_4305_ = lean_st_ref_get(v___y_4304_);
v_env_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc_ref(v_env_4306_);
lean_dec(v___x_4305_);
lean_inc(v_decl_4248_);
v___x_4307_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4306_, v_decl_4248_);
if (lean_obj_tag(v___x_4307_) == 1)
{
lean_object* v_val_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
lean_dec_ref(v___y_4302_);
lean_dec(v___x_4243_);
v_val_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_val_4308_);
lean_dec_ref(v___x_4307_);
v___x_4309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4310_ = 0;
v___x_4311_ = l_Lean_MessageData_ofConstName(v_decl_4248_, v___x_4310_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4309_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l_Lean_MessageData_ofConstName(v_val_4308_, v___x_4310_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v___x_4309_);
v___x_4318_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4249_, v___x_4317_, v___y_4303_, v___y_4304_);
lean_dec(v_stx_4249_);
return v___x_4318_;
}
else
{
lean_dec(v___x_4307_);
lean_dec(v_stx_4249_);
v___y_4284_ = v___y_4302_;
v___y_4285_ = v___y_4303_;
v___y_4286_ = v___y_4304_;
goto v___jp_4283_;
}
}
v___jp_4319_:
{
lean_object* v___x_4324_; lean_object* v_env_4325_; lean_object* v___x_4326_; 
v___x_4324_ = lean_st_ref_get(v___y_4323_);
v_env_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc_ref(v_env_4325_);
lean_dec(v___x_4324_);
v___x_4326_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4325_, v_decl_4248_);
lean_dec_ref(v_env_4325_);
if (lean_obj_tag(v___x_4326_) == 1)
{
lean_object* v_val_4327_; lean_object* v___x_4328_; lean_object* v_env_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
lean_dec_ref(v___y_4321_);
lean_dec(v___x_4243_);
v_val_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_val_4327_);
lean_dec_ref(v___x_4326_);
v___x_4328_ = lean_st_ref_get(v___y_4323_);
v_env_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc_ref(v_env_4329_);
lean_dec(v___x_4328_);
v___x_4330_ = l_Lean_Environment_allImportedModuleNames(v_env_4329_);
lean_dec_ref(v_env_4329_);
v___x_4331_ = lean_array_get_size(v___x_4330_);
v___x_4332_ = lean_nat_dec_lt(v_val_4327_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref(v___x_4330_);
lean_dec(v_val_4327_);
v___x_4333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4334_ = l_Lean_MessageData_ofConstName(v_decl_4248_, v___y_4320_);
v___x_4335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4333_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
v___x_4336_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4249_, v___x_4337_, v___y_4322_, v___y_4323_);
lean_dec(v_stx_4249_);
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4339_ = lean_array_fget(v___x_4330_, v_val_4327_);
lean_dec(v_val_4327_);
lean_dec_ref(v___x_4330_);
v___x_4340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4341_ = l_Lean_MessageData_ofConstName(v_decl_4248_, v___y_4320_);
v___x_4342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4340_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = l_Lean_MessageData_ofName(v___x_4339_);
v___x_4346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v___x_4347_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4346_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4249_, v___x_4348_, v___y_4322_, v___y_4323_);
lean_dec(v_stx_4249_);
return v___x_4349_;
}
}
else
{
lean_dec(v___x_4326_);
v___y_4302_ = v___y_4321_;
v___y_4303_ = v___y_4322_;
v___y_4304_ = v___y_4323_;
goto v___jp_4301_;
}
}
v___jp_4350_:
{
lean_object* v___x_4354_; lean_object* v_env_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v___x_4354_ = lean_st_ref_get(v___y_4353_);
v_env_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc_ref(v_env_4355_);
lean_dec(v___x_4354_);
v___x_4356_ = 0;
lean_inc(v_decl_4248_);
v___x_4357_ = l_Lean_Environment_find_x3f(v_env_4355_, v_decl_4248_, v___x_4356_);
if (lean_obj_tag(v___x_4357_) == 0)
{
v___y_4302_ = v_name_4351_;
v___y_4303_ = v___y_4352_;
v___y_4304_ = v___y_4353_;
goto v___jp_4301_;
}
else
{
lean_object* v___x_4358_; lean_object* v_env_4359_; uint8_t v___x_4360_; 
lean_dec_ref(v___x_4357_);
v___x_4358_ = lean_st_ref_get(v___y_4353_);
v_env_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc_ref(v_env_4359_);
lean_dec(v___x_4358_);
v___x_4360_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4359_, v_decl_4248_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
lean_dec_ref(v_name_4351_);
lean_dec(v___x_4243_);
v___x_4361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4362_ = l_Lean_MessageData_ofConstName(v_decl_4248_, v___x_4356_);
v___x_4363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
v___x_4364_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_4249_, v___x_4365_, v___y_4352_, v___y_4353_);
lean_dec(v_stx_4249_);
return v___x_4366_;
}
else
{
v___y_4320_ = v___x_4356_;
v___y_4321_ = v_name_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
goto v___jp_4319_;
}
}
}
v___jp_4367_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4368_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4369_ = l_Lean_Name_mkStr4(v___x_4244_, v___x_4245_, v___x_4368_, v___x_4246_);
lean_inc(v_stx_4249_);
v___x_4370_ = l_Lean_Syntax_isOfKind(v_stx_4249_, v___x_4369_);
lean_dec(v___x_4369_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_stx_4249_);
lean_dec(v_decl_4248_);
lean_dec(v___x_4243_);
v___x_4371_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4372_ = l_Lean_MessageData_ofName(v_name_4247_);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4375_, v___y_4251_, v___y_4252_);
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
v_name_4386_ = l_Lean_Syntax_getArg(v_stx_4249_, v___x_4385_);
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
lean_dec(v_stx_4249_);
lean_dec(v_decl_4248_);
lean_dec(v___x_4243_);
v___x_4391_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4392_ = l_Lean_MessageData_ofName(v_name_4247_);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4395_, v___y_4251_, v___y_4252_);
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
lean_dec(v_name_4247_);
v___x_4405_ = l_Lean_TSyntax_getId(v_name_4386_);
lean_dec(v_name_4386_);
v___x_4406_ = l_Lean_Name_toString(v___x_4405_, v___x_4388_);
v_name_4351_ = v___x_4406_;
v___y_4352_ = v___y_4251_;
v___y_4353_ = v___y_4252_;
goto v___jp_4350_;
}
}
else
{
lean_object* v___x_4407_; 
lean_dec(v_name_4247_);
v___x_4407_ = l_Lean_TSyntax_getString(v_name_4386_);
lean_dec(v_name_4386_);
v_name_4351_ = v___x_4407_;
v___y_4352_ = v___y_4251_;
v___y_4353_ = v___y_4252_;
goto v___jp_4350_;
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
lean_object* v___x_4493_; uint8_t v___x_4494_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4532_; lean_object* v___y_4533_; 
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
v___y_4532_ = v___y_4490_;
v___y_4533_ = v___y_4491_;
goto v___jp_4531_;
}
else
{
goto v___jp_4545_;
}
}
else
{
lean_dec_ref(v___x_4553_);
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
lean_dec_ref(v___x_4506_);
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
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4523_ = l_Lean_MessageData_ofConstName(v_declName_4488_, v___x_4494_);
v___x_4524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4522_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___x_4525_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4524_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4526_, v___y_4520_, v___y_4521_);
return v___x_4527_;
}
v___jp_4528_:
{
if (v___x_4494_ == 0)
{
v___y_4496_ = v___y_4529_;
v___y_4497_ = v___y_4530_;
goto v___jp_4495_;
}
else
{
v___y_4520_ = v___y_4529_;
v___y_4521_ = v___y_4530_;
goto v___jp_4519_;
}
}
v___jp_4531_:
{
lean_object* v___x_4534_; lean_object* v_env_4535_; lean_object* v___x_4536_; lean_object* v_toEnvExtension_4537_; lean_object* v_asyncMode_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4534_ = lean_st_ref_get(v___y_4533_);
v_env_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc_ref(v_env_4535_);
lean_dec(v___x_4534_);
v___x_4536_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4537_ = lean_ctor_get(v___x_4536_, 0);
v_asyncMode_4538_ = lean_ctor_get(v_toEnvExtension_4537_, 2);
v___x_4539_ = lean_box(1);
v___x_4540_ = lean_box(0);
v___x_4541_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4539_, v___x_4536_, v_env_4535_, v_asyncMode_4538_, v___x_4540_);
v___x_4542_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4541_, v_declName_4488_);
lean_dec(v___x_4541_);
if (lean_obj_tag(v___x_4542_) == 1)
{
lean_object* v_val_4543_; 
v_val_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_val_4543_);
lean_dec_ref(v___x_4542_);
if (lean_obj_tag(v_val_4543_) == 0)
{
lean_dec_ref(v_val_4543_);
if (v___x_4494_ == 0)
{
v___y_4520_ = v___y_4532_;
v___y_4521_ = v___y_4533_;
goto v___jp_4519_;
}
else
{
v___y_4529_ = v___y_4532_;
v___y_4530_ = v___y_4533_;
goto v___jp_4528_;
}
}
else
{
v___y_4529_ = v___y_4532_;
v___y_4530_ = v___y_4533_;
goto v___jp_4528_;
}
}
else
{
lean_dec(v___x_4542_);
v___y_4496_ = v___y_4532_;
v___y_4497_ = v___y_4533_;
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
