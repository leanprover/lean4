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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
static const lean_ctor_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
static const lean_closure_object l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_104_; 
v_es_83_ = lean_ctor_get(v_x_80_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_104_ == 0)
{
v___x_85_ = v_x_80_;
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_es_83_);
lean_dec(v_x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; lean_object* v_j_91_; lean_object* v___x_92_; 
v___x_87_ = lean_box(2);
v___x_88_ = ((size_t)5ULL);
v___x_89_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1);
v___x_90_ = lean_usize_land(v_x_81_, v___x_89_);
v_j_91_ = lean_usize_to_nat(v___x_90_);
v___x_92_ = lean_array_get(v___x_87_, v_es_83_, v_j_91_);
lean_dec(v_j_91_);
lean_dec_ref(v_es_83_);
switch(lean_obj_tag(v___x_92_))
{
case 0:
{
lean_object* v_key_93_; lean_object* v_val_94_; uint8_t v___x_95_; 
v_key_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_key_93_);
v_val_94_ = lean_ctor_get(v___x_92_, 1);
lean_inc(v_val_94_);
lean_dec_ref(v___x_92_);
v___x_95_ = lean_name_eq(v_x_82_, v_key_93_);
lean_dec(v_key_93_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec(v_val_94_);
lean_del_object(v___x_85_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_98_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 1);
lean_ctor_set(v___x_85_, 0, v_val_94_);
v___x_98_ = v___x_85_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_val_94_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
case 1:
{
lean_object* v_node_100_; size_t v___x_101_; 
lean_del_object(v___x_85_);
v_node_100_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_node_100_);
lean_dec_ref(v___x_92_);
v___x_101_ = lean_usize_shift_right(v_x_81_, v___x_88_);
v_x_80_ = v_node_100_;
v_x_81_ = v___x_101_;
goto _start;
}
default: 
{
lean_object* v___x_103_; 
lean_del_object(v___x_85_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
}
}
else
{
lean_object* v_ks_105_; lean_object* v_vs_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_ks_105_ = lean_ctor_get(v_x_80_, 0);
lean_inc_ref(v_ks_105_);
v_vs_106_ = lean_ctor_get(v_x_80_, 1);
lean_inc_ref(v_vs_106_);
lean_dec_ref(v_x_80_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_ks_105_, v_vs_106_, v___x_107_, v_x_82_);
lean_dec_ref(v_vs_106_);
lean_dec_ref(v_ks_105_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg___boxed(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
size_t v_x_468__boxed_112_; lean_object* v_res_113_; 
v_x_468__boxed_112_ = lean_unbox_usize(v_x_110_);
lean_dec(v_x_110_);
v_res_113_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_109_, v_x_468__boxed_112_, v_x_111_);
lean_dec(v_x_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint64_t v___y_117_; 
if (lean_obj_tag(v_x_115_) == 0)
{
uint64_t v___x_120_; 
v___x_120_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_117_ = v___x_120_;
goto v___jp_116_;
}
else
{
uint64_t v_hash_121_; 
v_hash_121_ = lean_ctor_get_uint64(v_x_115_, sizeof(void*)*2);
v___y_117_ = v_hash_121_;
goto v___jp_116_;
}
v___jp_116_:
{
size_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_uint64_to_usize(v___y_117_);
v___x_119_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_114_, v___x_118_, v_x_115_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg___boxed(lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_122_, v_x_123_);
lean_dec(v_x_123_);
return v_res_124_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object* v_env_128_, lean_object* v_kind_129_){
_start:
{
lean_object* v___x_130_; lean_object* v_ext_131_; lean_object* v_toEnvExtension_132_; lean_object* v_asyncMode_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_categories_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_130_ = l_Lean_Parser_parserExtension;
v_ext_131_ = lean_ctor_get(v___x_130_, 1);
v_toEnvExtension_132_ = lean_ctor_get(v_ext_131_, 0);
v_asyncMode_133_ = lean_ctor_get(v_toEnvExtension_132_, 2);
v___x_134_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_135_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_134_, v___x_130_, v_env_128_, v_asyncMode_133_);
v_categories_136_ = lean_ctor_get(v___x_135_, 2);
lean_inc_ref(v_categories_136_);
lean_dec(v___x_135_);
v___x_137_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_138_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_categories_136_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 1)
{
lean_object* v_val_139_; lean_object* v_kinds_140_; uint8_t v___x_141_; 
v_val_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_val_139_);
lean_dec_ref(v___x_138_);
v_kinds_140_ = lean_ctor_get(v_val_139_, 1);
lean_inc_ref(v_kinds_140_);
lean_dec(v_val_139_);
v___x_141_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_140_, v_kind_129_);
lean_dec_ref(v_kinds_140_);
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
lean_dec(v___x_138_);
v___x_142_ = 0;
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_isTactic___boxed(lean_object* v_env_143_, lean_object* v_kind_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_143_, v_kind_144_);
lean_dec(v_kind_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(lean_object* v_00_u03b2_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___redArg(v_x_148_, v_x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0___boxed(lean_object* v_00_u03b2_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0(v_00_u03b2_151_, v_x_152_, v_x_153_);
lean_dec(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(lean_object* v_00_u03b2_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_x_156_, v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___boxed(lean_object* v_00_u03b2_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1(v_00_u03b2_159_, v_x_160_, v_x_161_);
lean_dec(v_x_161_);
lean_dec_ref(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(lean_object* v_00_u03b2_164_, lean_object* v_x_165_, size_t v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___redArg(v_x_165_, v_x_166_, v_x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
size_t v_x_589__boxed_173_; lean_object* v_res_174_; 
v_x_589__boxed_173_ = lean_unbox_usize(v_x_171_);
lean_dec(v_x_171_);
v_res_174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0(v_00_u03b2_169_, v_x_170_, v_x_589__boxed_173_, v_x_172_);
lean_dec(v_x_172_);
return v_res_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(lean_object* v_00_u03b2_175_, lean_object* v_x_176_, size_t v_x_177_, lean_object* v_x_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg(v_x_176_, v_x_177_, v_x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___boxed(lean_object* v_00_u03b2_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
size_t v_x_600__boxed_184_; uint8_t v_res_185_; lean_object* v_r_186_; 
v_x_600__boxed_184_ = lean_unbox_usize(v_x_182_);
lean_dec(v_x_182_);
v_res_185_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2(v_00_u03b2_180_, v_x_181_, v_x_600__boxed_184_, v_x_183_);
lean_dec(v_x_183_);
lean_dec_ref(v_x_181_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_187_, lean_object* v_keys_188_, lean_object* v_vals_189_, lean_object* v_heq_190_, lean_object* v_i_191_, lean_object* v_k_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___redArg(v_keys_188_, v_vals_189_, v_i_191_, v_k_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_194_, lean_object* v_keys_195_, lean_object* v_vals_196_, lean_object* v_heq_197_, lean_object* v_i_198_, lean_object* v_k_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_Tactic_Doc_isTactic_spec__0_spec__0_spec__1(v_00_u03b2_194_, v_keys_195_, v_vals_196_, v_heq_197_, v_i_198_, v_k_199_);
lean_dec(v_k_199_);
lean_dec_ref(v_vals_196_);
lean_dec_ref(v_keys_195_);
return v_res_200_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_201_, lean_object* v_keys_202_, lean_object* v_vals_203_, lean_object* v_heq_204_, lean_object* v_i_205_, lean_object* v_k_206_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___redArg(v_keys_202_, v_i_205_, v_k_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_208_, lean_object* v_keys_209_, lean_object* v_vals_210_, lean_object* v_heq_211_, lean_object* v_i_212_, lean_object* v_k_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2_spec__4(v_00_u03b2_208_, v_keys_209_, v_vals_210_, v_heq_211_, v_i_212_, v_k_213_);
lean_dec(v_k_213_);
lean_dec_ref(v_vals_210_);
lean_dec_ref(v_keys_209_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_as_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_fst_218_; lean_object* v_snd_219_; lean_object* v___x_220_; 
v_fst_218_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_fst_218_);
v_snd_219_ = lean_ctor_get(v_x_217_, 1);
lean_inc(v_snd_219_);
lean_dec_ref(v_x_217_);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_218_, v_snd_219_, v_as_216_);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_221_, lean_object* v_x2_222_){
_start:
{
lean_object* v_fst_223_; lean_object* v_fst_224_; uint8_t v___x_225_; 
v_fst_223_ = lean_ctor_get(v_x1_221_, 0);
v_fst_224_ = lean_ctor_get(v_x2_222_, 0);
v___x_225_ = l_Lean_Name_quickLt(v_fst_223_, v_fst_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_226_, lean_object* v_x2_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_226_, v_x2_227_);
lean_dec_ref(v_x2_227_);
lean_dec_ref(v_x1_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_231_, lean_object* v_lo_232_, lean_object* v_hi_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_nat_dec_lt(v_lo_232_, v_hi_233_);
if (v___x_234_ == 0)
{
lean_dec(v_lo_232_);
return v_as_231_;
}
else
{
lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; uint8_t v___x_239_; 
v___f_235_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_232_);
v___x_236_ = l_Array_qpartition___redArg(v_as_231_, v___f_235_, v_lo_232_, v_hi_233_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_fst_237_);
v_snd_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_snd_238_);
lean_dec_ref(v___x_236_);
v___x_239_ = lean_nat_dec_le(v_hi_233_, v_fst_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_snd_238_, v_lo_232_, v_fst_237_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_fst_237_, v___x_241_);
lean_dec(v_fst_237_);
v_as_231_ = v___x_240_;
v_lo_232_ = v___x_242_;
goto _start;
}
else
{
lean_dec(v_fst_237_);
lean_dec(v_lo_232_);
return v_snd_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_244_, lean_object* v_lo_245_, lean_object* v_hi_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_as_244_, v_lo_245_, v_hi_246_);
lean_dec(v_hi_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_k_250_; lean_object* v_v_251_; lean_object* v_l_252_; lean_object* v_r_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_k_250_ = lean_ctor_get(v_x_249_, 1);
v_v_251_ = lean_ctor_get(v_x_249_, 2);
v_l_252_ = lean_ctor_get(v_x_249_, 3);
v_r_253_ = lean_ctor_get(v_x_249_, 4);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_248_, v_l_252_);
lean_inc(v_v_251_);
lean_inc(v_k_250_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_k_250_);
lean_ctor_set(v___x_255_, 1, v_v_251_);
v___x_256_ = lean_array_push(v___x_254_, v___x_255_);
v_init_248_ = v___x_256_;
v_x_249_ = v_r_253_;
goto _start;
}
else
{
return v_init_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_258_, v_x_259_);
lean_dec(v_x_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_263_, lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_267_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_266_, v_s_264_);
v___x_273_ = lean_array_get_size(v___x_267_);
v___x_274_ = lean_nat_dec_eq(v___x_273_, v___x_265_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___y_278_; uint8_t v___x_280_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_sub(v___x_273_, v___x_275_);
v___x_280_ = lean_nat_dec_le(v___x_265_, v___x_276_);
if (v___x_280_ == 0)
{
lean_inc(v___x_276_);
v___y_278_ = v___x_276_;
goto v___jp_277_;
}
else
{
v___y_278_ = v___x_265_;
goto v___jp_277_;
}
v___jp_277_:
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___y_278_, v___x_276_);
if (v___x_279_ == 0)
{
lean_dec(v___x_276_);
lean_inc(v___y_278_);
v___y_269_ = v___y_278_;
v___y_270_ = v___y_278_;
goto v___jp_268_;
}
else
{
v___y_269_ = v___y_278_;
v___y_270_ = v___x_276_;
goto v___jp_268_;
}
}
}
else
{
lean_object* v___x_281_; 
lean_inc_ref_n(v___x_267_, 2);
v___x_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_267_);
lean_ctor_set(v___x_281_, 1, v___x_267_);
lean_ctor_set(v___x_281_, 2, v___x_267_);
return v___x_281_;
}
v___jp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_267_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_inc_ref_n(v___x_271_, 2);
v___x_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_282_, lean_object* v_s_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_282_, v_s_283_);
lean_dec(v_s_283_);
lean_dec_ref(v_x_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_x_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_x_287_);
lean_dec(v_x_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v_es_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_292_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v___x_291_, v_es_289_);
v___x_293_ = lean_array_get_size(v___x_292_);
v___x_294_ = lean_nat_dec_eq(v___x_293_, v___x_290_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___y_298_; uint8_t v___x_302_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_sub(v___x_293_, v___x_295_);
v___x_302_ = lean_nat_dec_le(v___x_290_, v___x_296_);
if (v___x_302_ == 0)
{
lean_inc(v___x_296_);
v___y_298_ = v___x_296_;
goto v___jp_297_;
}
else
{
v___y_298_ = v___x_290_;
goto v___jp_297_;
}
v___jp_297_:
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_le(v___y_298_, v___x_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v___x_296_);
lean_inc(v___y_298_);
v___x_300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_292_, v___y_298_, v___y_298_);
lean_dec(v___y_298_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v___x_292_, v___y_298_, v___x_296_);
lean_dec(v___x_296_);
return v___x_301_;
}
}
}
else
{
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_es_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v_es_303_);
lean_dec(v_es_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(lean_object* v___x_311_, lean_object* v_x_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_311_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v___x_316_, lean_object* v_x_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__5_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(v___x_316_, v_x_317_, v___y_318_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_x_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__13_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_354_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_();
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(lean_object* v_init_357_, lean_object* v_t_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0_spec__0(v_init_357_, v_t_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_360_, lean_object* v_t_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__0(v_init_360_, v_t_361_);
lean_dec(v_t_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(lean_object* v_n_363_, lean_object* v_as_364_, lean_object* v_lo_365_, lean_object* v_hi_366_, lean_object* v_w_367_, lean_object* v_hlo_368_, lean_object* v_hhi_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg(v_as_364_, v_lo_365_, v_hi_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_371_, lean_object* v_as_372_, lean_object* v_lo_373_, lean_object* v_hi_374_, lean_object* v_w_375_, lean_object* v_hlo_376_, lean_object* v_hhi_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1(v_n_371_, v_as_372_, v_lo_373_, v_hi_374_, v_w_375_, v_hlo_376_, v_hhi_377_);
lean_dec(v_hi_374_);
lean_dec(v_n_371_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(lean_object* v_as_379_, lean_object* v_k_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_m_385_; lean_object* v_a_386_; uint8_t v___x_387_; 
v___x_383_ = lean_nat_add(v_x_381_, v_x_382_);
v___x_384_ = lean_unsigned_to_nat(1u);
v_m_385_ = lean_nat_shiftr(v___x_383_, v___x_384_);
lean_dec(v___x_383_);
v_a_386_ = lean_array_fget_borrowed(v_as_379_, v_m_385_);
v___x_387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_386_, v_k_380_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; 
lean_dec(v_x_382_);
v___x_388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_380_, v_a_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v_m_385_);
lean_dec(v_x_381_);
lean_inc(v_a_386_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_a_386_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_eq(v_m_385_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_nat_sub(v_m_385_, v___x_384_);
lean_dec(v_m_385_);
v___x_393_ = lean_nat_dec_lt(v___x_392_, v_x_381_);
if (v___x_393_ == 0)
{
v_x_382_ = v___x_392_;
goto _start;
}
else
{
lean_object* v___x_395_; 
lean_dec(v___x_392_);
lean_dec(v_x_381_);
v___x_395_ = lean_box(0);
return v___x_395_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v_m_385_);
lean_dec(v_x_381_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
}
else
{
lean_object* v___x_397_; uint8_t v___x_398_; 
lean_dec(v_x_381_);
v___x_397_ = lean_nat_add(v_m_385_, v___x_384_);
lean_dec(v_m_385_);
v___x_398_ = lean_nat_dec_le(v___x_397_, v_x_382_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___x_397_);
lean_dec(v_x_382_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
v_x_381_ = v___x_397_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg___boxed(lean_object* v_as_401_, lean_object* v_k_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_401_, v_k_402_, v_x_403_, v_x_404_);
lean_dec_ref(v_k_402_);
lean_dec_ref(v_as_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object* v_env_406_, lean_object* v_tac_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(1);
v___x_409_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_406_, v_tac_407_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v_toEnvExtension_411_; lean_object* v_asyncMode_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_411_ = lean_ctor_get(v___x_410_, 0);
v_asyncMode_412_ = lean_ctor_get(v_toEnvExtension_411_, 2);
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_408_, v___x_410_, v_env_406_, v_asyncMode_412_, v___x_413_);
v___x_415_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_414_, v_tac_407_);
lean_dec(v_tac_407_);
lean_dec(v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_val_416_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_416_);
lean_dec_ref(v___x_409_);
v___x_417_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v___x_418_ = 0;
v___x_419_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_408_, v___x_417_, v_env_406_, v_val_416_, v___x_418_);
lean_dec(v_val_416_);
lean_dec_ref(v_env_406_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_array_get_size(v___x_419_);
v___x_422_ = lean_nat_dec_lt(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v___x_419_);
lean_dec(v_tac_407_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_sub(v___x_421_, v___x_424_);
v___x_426_ = lean_nat_dec_le(v___x_420_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_dec(v___x_425_);
lean_dec_ref(v___x_419_);
lean_dec(v_tac_407_);
v___x_427_ = lean_box(0);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_tac_407_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v___x_419_, v___x_429_, v___x_420_, v___x_425_);
lean_dec_ref(v___x_429_);
lean_dec_ref(v___x_419_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_val_432_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_430_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_val_432_);
lean_dec(v___x_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_snd_436_; lean_object* v___x_438_; 
v_snd_436_ = lean_ctor_get(v_val_432_, 1);
lean_inc(v_snd_436_);
lean_dec(v_val_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_snd_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_snd_436_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(lean_object* v_as_441_, lean_object* v_k_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___redArg(v_as_441_, v_k_442_, v_x_443_, v_x_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0___boxed(lean_object* v_as_447_, lean_object* v_k_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_alternativeOfTactic_spec__0(v_as_447_, v_k_448_, v_x_449_, v_x_450_, v_x_451_);
lean_dec_ref(v_k_448_);
lean_dec_ref(v_as_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0(lean_object* v_toPure_453_, lean_object* v_____do__lift_454_){
_start:
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v_____do__lift_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref(v_____do__lift_454_);
v___x_456_ = lean_apply_2(v_toPure_453_, lean_box(0), v_a_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(lean_object* v_tac_457_, lean_object* v_toPure_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_c_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_name_eq(v_b_460_, v_tac_457_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_a_459_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_c_461_);
v___x_464_ = lean_apply_2(v_toPure_458_, lean_box(0), v___x_463_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = l_Lean_NameSet_insert(v_c_461_, v_a_459_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = lean_apply_2(v_toPure_458_, lean_box(0), v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed(lean_object* v_tac_468_, lean_object* v_toPure_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v_c_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1(v_tac_468_, v_toPure_469_, v_a_470_, v_b_471_, v_c_472_);
lean_dec(v_b_471_);
lean_dec(v_tac_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(lean_object* v_tac_474_, lean_object* v_toPure_475_, lean_object* v_a_476_, lean_object* v_x_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_fst_479_; lean_object* v_snd_480_; uint8_t v___x_481_; 
v_fst_479_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_fst_479_);
v_snd_480_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_snd_480_);
lean_dec_ref(v_a_476_);
v___x_481_ = lean_name_eq(v_snd_480_, v_tac_474_);
lean_dec(v_snd_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_fst_479_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___y_478_);
v___x_483_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_482_);
return v___x_483_;
}
else
{
lean_object* v_found_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_found_484_ = l_Lean_NameSet_insert(v___y_478_, v_fst_479_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_found_484_);
v___x_486_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed(lean_object* v_tac_487_, lean_object* v_toPure_488_, lean_object* v_a_489_, lean_object* v_x_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2(v_tac_487_, v_toPure_488_, v_a_489_, v_x_490_, v___y_491_);
lean_dec(v_tac_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3(lean_object* v_toPure_493_, lean_object* v_____s_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_____s_494_);
v___x_496_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4(lean_object* v_inst_497_, lean_object* v___f_498_, lean_object* v_toBind_499_, lean_object* v___f_500_, lean_object* v_a_501_, lean_object* v_x_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_504_; size_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_sz_504_ = lean_array_size(v_a_501_);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_497_, v_a_501_, v___f_498_, v_sz_504_, v___x_505_, v___y_503_);
v___x_507_ = lean_apply_4(v_toBind_499_, lean_box(0), lean_box(0), v___x_506_, v___f_500_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5(lean_object* v_toPure_508_, lean_object* v_____s_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_apply_2(v_toPure_508_, lean_box(0), v_____s_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(lean_object* v___x_511_, lean_object* v_toEnvExtension_512_, lean_object* v_env_513_, lean_object* v_asyncMode_514_, lean_object* v___x_515_, lean_object* v_inst_516_, lean_object* v___f_517_, lean_object* v_toBind_518_, lean_object* v___f_519_, lean_object* v_____s_520_){
_start:
{
lean_object* v___x_521_; lean_object* v_importedEntries_522_; size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_521_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_511_, v_toEnvExtension_512_, v_env_513_, v_asyncMode_514_, v___x_515_);
v_importedEntries_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_importedEntries_522_);
lean_dec(v___x_521_);
v_sz_523_ = lean_array_size(v_importedEntries_522_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_516_, v_importedEntries_522_, v___f_517_, v_sz_523_, v___x_524_, v_____s_520_);
v___x_526_ = lean_apply_4(v_toBind_518_, lean_box(0), lean_box(0), v___x_525_, v___f_519_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed(lean_object* v___x_527_, lean_object* v_toEnvExtension_528_, lean_object* v_env_529_, lean_object* v_asyncMode_530_, lean_object* v___x_531_, lean_object* v_inst_532_, lean_object* v___f_533_, lean_object* v_toBind_534_, lean_object* v___f_535_, lean_object* v_____s_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6(v___x_527_, v_toEnvExtension_528_, v_env_529_, v_asyncMode_530_, v___x_531_, v_inst_532_, v___f_533_, v_toBind_534_, v___f_535_, v_____s_536_);
lean_dec(v_asyncMode_530_);
lean_dec_ref(v_toEnvExtension_528_);
lean_dec_ref(v___x_527_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7(lean_object* v___x_538_, lean_object* v_inst_539_, lean_object* v___f_540_, lean_object* v_toBind_541_, lean_object* v___f_542_, lean_object* v___x_543_, lean_object* v___f_544_, lean_object* v___f_545_, lean_object* v_env_546_){
_start:
{
lean_object* v___x_547_; lean_object* v_toEnvExtension_548_; lean_object* v_asyncMode_549_; lean_object* v_found_550_; lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_547_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_548_ = lean_ctor_get(v___x_547_, 0);
v_asyncMode_549_ = lean_ctor_get(v_toEnvExtension_548_, 2);
v_found_550_ = l_Lean_NameSet_empty;
v___x_551_ = lean_box(0);
lean_inc_n(v_toBind_541_, 2);
lean_inc_ref(v_inst_539_);
lean_inc(v_asyncMode_549_);
lean_inc_ref(v_env_546_);
lean_inc_ref(v_toEnvExtension_548_);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_552_, 0, v___x_538_);
lean_closure_set(v___f_552_, 1, v_toEnvExtension_548_);
lean_closure_set(v___f_552_, 2, v_env_546_);
lean_closure_set(v___f_552_, 3, v_asyncMode_549_);
lean_closure_set(v___f_552_, 4, v___x_551_);
lean_closure_set(v___f_552_, 5, v_inst_539_);
lean_closure_set(v___f_552_, 6, v___f_540_);
lean_closure_set(v___f_552_, 7, v_toBind_541_);
lean_closure_set(v___f_552_, 8, v___f_542_);
v___x_553_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_543_, v___x_547_, v_env_546_, v_asyncMode_549_, v___x_551_);
v___x_554_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_539_, v___f_544_, v_found_550_, v___x_553_);
v___x_555_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v___x_554_, v___f_545_);
v___x_556_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v___x_555_, v___f_552_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(1);
v___x_558_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases___redArg(lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_tac_561_){
_start:
{
lean_object* v_toApplicative_562_; lean_object* v_toBind_563_; lean_object* v_getEnv_564_; lean_object* v_toPure_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
v_toApplicative_562_ = lean_ctor_get(v_inst_559_, 0);
v_toBind_563_ = lean_ctor_get(v_inst_559_, 1);
lean_inc_n(v_toBind_563_, 3);
v_getEnv_564_ = lean_ctor_get(v_inst_560_, 0);
lean_inc(v_getEnv_564_);
lean_dec_ref(v_inst_560_);
v_toPure_565_ = lean_ctor_get(v_toApplicative_562_, 1);
v___x_566_ = lean_box(1);
v___x_567_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0, &l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_aliases___redArg___closed__0);
lean_inc_n(v_toPure_565_, 5);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_568_, 0, v_toPure_565_);
lean_inc(v_tac_561_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_569_, 0, v_tac_561_);
lean_closure_set(v___f_569_, 1, v_toPure_565_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_570_, 0, v_tac_561_);
lean_closure_set(v___f_570_, 1, v_toPure_565_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_571_, 0, v_toPure_565_);
lean_inc_ref(v_inst_559_);
v___f_572_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__4), 7, 4);
lean_closure_set(v___f_572_, 0, v_inst_559_);
lean_closure_set(v___f_572_, 1, v___f_570_);
lean_closure_set(v___f_572_, 2, v_toBind_563_);
lean_closure_set(v___f_572_, 3, v___f_571_);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__5), 2, 1);
lean_closure_set(v___f_573_, 0, v_toPure_565_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__7), 9, 8);
lean_closure_set(v___f_574_, 0, v___x_567_);
lean_closure_set(v___f_574_, 1, v_inst_559_);
lean_closure_set(v___f_574_, 2, v___f_572_);
lean_closure_set(v___f_574_, 3, v_toBind_563_);
lean_closure_set(v___f_574_, 4, v___f_573_);
lean_closure_set(v___f_574_, 5, v___x_566_);
lean_closure_set(v___f_574_, 6, v___f_569_);
lean_closure_set(v___f_574_, 7, v___f_568_);
v___x_575_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v_getEnv_564_, v___f_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_aliases(lean_object* v_m_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_tac_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Parser_Tactic_Doc_aliases___redArg(v_inst_577_, v_inst_578_, v_tac_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_581_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_ctor_set(v___x_586_, 2, v___x_585_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
lean_ctor_set(v___x_586_, 4, v___x_584_);
lean_ctor_set(v___x_586_, 5, v___x_584_);
lean_ctor_set(v___x_586_, 6, v___x_584_);
lean_ctor_set(v___x_586_, 7, v___x_584_);
lean_ctor_set(v___x_586_, 8, v___x_584_);
lean_ctor_set(v___x_586_, 9, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((size_t)5ULL);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_unsigned_to_nat(32u);
v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
v___x_594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_595_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_591_);
lean_ctor_set(v___x_595_, 3, v___x_591_);
lean_ctor_set_usize(v___x_595_, 4, v___x_590_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = lean_box(1);
v___x_597_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_ctor_set(v___x_599_, 2, v___x_596_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_env_605_; lean_object* v_options_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_604_ = lean_st_ref_get(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v_options_606_ = lean_ctor_get(v___y_601_, 2);
v___x_607_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_606_);
v___x_609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_609_, 0, v_env_605_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
lean_ctor_set(v___x_609_, 3, v_options_606_);
v___x_610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_msgData_600_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msgData_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_ref_621_; lean_object* v___x_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_ref_621_ = lean_ctor_get(v___y_618_, 5);
v___x_622_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_617_, v___y_618_, v___y_619_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc(v_ref_621_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_ref_621_);
lean_ctor_set(v___x_627_, 1, v_a_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 1);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_name_643_, lean_object* v_decl_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_649_ = l_Lean_MessageData_ofName(v_name_643_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_652_, v___y_645_, v___y_646_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_name_654_, lean_object* v_decl_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_name_654_, v_decl_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v_decl_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v_decl_660_, lean_object* v_x_661_, lean_object* v_____s_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_snd_666_; lean_object* v_fst_667_; lean_object* v_kinds_668_; uint8_t v___x_669_; 
v_snd_666_ = lean_ctor_get(v_x_661_, 1);
lean_inc(v_snd_666_);
v_fst_667_ = lean_ctor_get(v_x_661_, 0);
lean_inc(v_fst_667_);
lean_dec_ref(v_x_661_);
v_kinds_668_ = lean_ctor_get(v_snd_666_, 1);
lean_inc_ref(v_kinds_668_);
lean_dec(v_snd_666_);
v___x_669_ = l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg(v_kinds_668_, v_decl_660_);
lean_dec_ref(v_kinds_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_fst_667_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_____s_662_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_array_push(v_____s_662_, v_fst_667_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_decl_675_, lean_object* v_x_676_, lean_object* v_____s_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v_decl_675_, v_x_676_, v_____s_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_decl_675_);
return v_res_681_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__0));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(size_t v_sz_685_, size_t v_i_686_, lean_object* v_bs_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_688_ == 0)
{
return v_bs_687_;
}
else
{
lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_bs_x27_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_v_689_ = lean_array_uget(v_bs_687_, v_i_686_);
v___x_690_ = lean_unsigned_to_nat(0u);
v_bs_x27_691_ = lean_array_uset(v_bs_687_, v_i_686_, v___x_690_);
v___x_692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_693_ = l_Lean_MessageData_ofName(v_v_689_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_692_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_686_, v___x_696_);
v___x_698_ = lean_array_uset(v_bs_x27_691_, v_i_686_, v___x_695_);
v_i_686_ = v___x_697_;
v_bs_687_ = v___x_698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___boxed(lean_object* v_sz_700_, lean_object* v_i_701_, lean_object* v_bs_702_){
_start:
{
size_t v_sz_boxed_703_; size_t v_i_boxed_704_; lean_object* v_res_705_; 
v_sz_boxed_703_ = lean_unbox_usize(v_sz_700_);
lean_dec(v_sz_700_);
v_i_boxed_704_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_boxed_703_, v_i_boxed_704_, v_bs_702_);
return v_res_705_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__0));
v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__2));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(lean_object* v_name_715_, uint8_t v_kind_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___y_726_; 
v___x_720_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__1);
v___x_721_ = l_Lean_MessageData_ofName(v_name_715_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__3);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
switch(v_kind_716_)
{
case 0:
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__4));
v___y_726_ = v___x_733_;
goto v___jp_725_;
}
case 1:
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__5));
v___y_726_ = v___x_734_;
goto v___jp_725_;
}
default: 
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___closed__6));
v___y_726_ = v___x_735_;
goto v___jp_725_;
}
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_inc_ref(v___y_726_);
v___x_727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_727_, 0, v___y_726_);
v___x_728_ = l_Lean_MessageData_ofFormat(v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_731_, v___y_717_, v___y_718_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg___boxed(lean_object* v_name_736_, lean_object* v_kind_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v_kind_boxed_741_; lean_object* v_res_742_; 
v_kind_boxed_741_ = lean_unbox(v_kind_737_);
v_res_742_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_736_, v_kind_boxed_741_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(lean_object* v_f_743_, lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_i_746_, lean_object* v_acc_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_keys_744_);
v___x_752_ = lean_nat_dec_lt(v_i_746_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_i_746_);
lean_dec_ref(v_f_743_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v_acc_747_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v___x_757_; 
v_k_755_ = lean_array_fget_borrowed(v_keys_744_, v_i_746_);
v_v_756_ = lean_array_fget_borrowed(v_vals_745_, v_i_746_);
lean_inc_ref(v_f_743_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v_v_756_);
lean_inc(v_k_755_);
v___x_757_ = lean_apply_6(v_f_743_, v_acc_747_, v_k_755_, v_v_756_, v___y_748_, v___y_749_, lean_box(0));
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
if (lean_obj_tag(v_a_758_) == 0)
{
lean_dec_ref(v_a_758_);
lean_dec(v_i_746_);
lean_dec_ref(v_f_743_);
return v___x_757_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v___x_757_);
v_a_759_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v_a_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_i_746_, v___x_760_);
lean_dec(v_i_746_);
v_i_746_ = v___x_761_;
v_acc_747_ = v_a_759_;
goto _start;
}
}
else
{
lean_dec(v_i_746_);
lean_dec_ref(v_f_743_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_f_763_, lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_i_766_, lean_object* v_acc_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_763_, v_keys_764_, v_vals_765_, v_i_766_, v_acc_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_vals_765_);
lean_dec_ref(v_keys_764_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_f_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_es_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_800_; 
v_es_778_ = lean_ctor_get(v_x_773_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_800_ == 0)
{
v___x_780_ = v_x_773_;
v_isShared_781_ = v_isSharedCheck_800_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_es_778_);
lean_dec(v_x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_800_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_array_get_size(v_es_778_);
v___x_784_ = lean_nat_dec_lt(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_es_778_);
lean_dec_ref(v_f_772_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 0, v_x_774_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_x_774_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_le(v___x_783_, v___x_783_);
if (v___x_789_ == 0)
{
if (v___x_784_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v_es_778_);
lean_dec_ref(v_f_772_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 0, v_x_774_);
v___x_791_ = v___x_780_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_x_774_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_780_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_of_nat(v___x_783_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_772_, v_es_778_, v___x_794_, v___x_795_, v_x_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_es_778_);
return v___x_796_;
}
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_780_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_of_nat(v___x_783_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_772_, v_es_778_, v___x_797_, v___x_798_, v_x_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_es_778_);
return v___x_799_;
}
}
}
}
else
{
lean_object* v_ks_801_; lean_object* v_vs_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_ks_801_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_ks_801_);
v_vs_802_ = lean_ctor_get(v_x_773_, 1);
lean_inc_ref(v_vs_802_);
lean_dec_ref(v_x_773_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_772_, v_ks_801_, v_vs_802_, v___x_803_, v_x_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_vs_802_);
lean_dec_ref(v_ks_801_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(lean_object* v_f_805_, lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_a_814_; lean_object* v___y_819_; uint8_t v___x_822_; 
v___x_822_ = lean_usize_dec_eq(v_i_807_, v_stop_808_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
v___x_823_ = lean_array_uget_borrowed(v_as_806_, v_i_807_);
switch(lean_obj_tag(v___x_823_))
{
case 0:
{
lean_object* v_key_824_; lean_object* v_val_825_; lean_object* v___x_826_; 
v_key_824_ = lean_ctor_get(v___x_823_, 0);
v_val_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc_ref(v_f_805_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v_val_825_);
lean_inc(v_key_824_);
v___x_826_ = lean_apply_6(v_f_805_, v_b_809_, v_key_824_, v_val_825_, v___y_810_, v___y_811_, lean_box(0));
v___y_819_ = v___x_826_;
goto v___jp_818_;
}
case 1:
{
lean_object* v_node_827_; lean_object* v___x_828_; 
v_node_827_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_node_827_);
lean_inc_ref(v_f_805_);
v___x_828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_805_, v_node_827_, v_b_809_, v___y_810_, v___y_811_);
v___y_819_ = v___x_828_;
goto v___jp_818_;
}
default: 
{
v_a_814_ = v_b_809_;
goto v___jp_813_;
}
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v_f_805_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_b_809_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
v___jp_813_:
{
size_t v___x_815_; size_t v___x_816_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_807_, v___x_815_);
v_i_807_ = v___x_816_;
v_b_809_ = v_a_814_;
goto _start;
}
v___jp_818_:
{
if (lean_obj_tag(v___y_819_) == 0)
{
lean_object* v_a_820_; 
v_a_820_ = lean_ctor_get(v___y_819_, 0);
if (lean_obj_tag(v_a_820_) == 0)
{
lean_dec_ref(v_f_805_);
return v___y_819_;
}
else
{
lean_object* v_a_821_; 
lean_inc_ref(v_a_820_);
lean_dec_ref(v___y_819_);
v_a_821_ = lean_ctor_get(v_a_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v_a_820_);
v_a_814_ = v_a_821_;
goto v___jp_813_;
}
}
else
{
lean_dec_ref(v_f_805_);
return v___y_819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_f_831_, lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
size_t v_i_boxed_839_; size_t v_stop_boxed_840_; lean_object* v_res_841_; 
v_i_boxed_839_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_840_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_831_, v_as_832_, v_i_boxed_839_, v_stop_boxed_840_, v_b_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v_as_832_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_842_, v_x_843_, v_x_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_f_849_, lean_object* v_s_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_a_851_);
lean_ctor_set(v___x_856_, 1, v_b_852_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_857_ = lean_apply_5(v_f_849_, v___x_856_, v_s_850_, v___y_853_, v___y_854_, lean_box(0));
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_884_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_884_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_884_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_884_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
if (lean_obj_tag(v_a_858_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_872_; 
v_a_862_ = lean_ctor_get(v_a_858_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_872_ == 0)
{
v___x_864_ = v_a_858_;
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v_a_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_867_);
v___x_869_ = v___x_860_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_a_873_ = lean_ctor_get(v_a_858_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_883_ == 0)
{
v___x_875_ = v_a_858_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_a_858_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_878_);
v___x_880_ = v___x_860_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_857_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_857_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_f_893_, lean_object* v_s_894_, lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0(v_f_893_, v_s_894_, v_a_895_, v_b_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(lean_object* v_map_901_, lean_object* v_init_902_, lean_object* v_f_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___f_907_; lean_object* v___x_908_; 
v___f_907_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_907_, 0, v_f_903_);
v___x_908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v___f_907_, v_map_901_, v_init_902_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_917_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_a_913_; lean_object* v___x_915_; 
v_a_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_a_913_);
lean_dec(v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_a_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_908_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_908_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_map_926_, lean_object* v_init_927_, lean_object* v_f_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_926_, v_init_927_, v_f_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_932_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_933_; double v___x_934_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_float_of_nat(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_cls_938_, lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_ref_943_; lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_989_; 
v_ref_943_ = lean_ctor_get(v___y_940_, 5);
v___x_944_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0_spec__0(v_msg_939_, v___y_940_, v___y_941_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_989_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_989_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_989_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v_traceState_950_; lean_object* v_env_951_; lean_object* v_nextMacroScope_952_; lean_object* v_ngen_953_; lean_object* v_auxDeclNGen_954_; lean_object* v_cache_955_; lean_object* v_messages_956_; lean_object* v_infoState_957_; lean_object* v_snapshotTasks_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_988_; 
v___x_949_ = lean_st_ref_take(v___y_941_);
v_traceState_950_ = lean_ctor_get(v___x_949_, 4);
v_env_951_ = lean_ctor_get(v___x_949_, 0);
v_nextMacroScope_952_ = lean_ctor_get(v___x_949_, 1);
v_ngen_953_ = lean_ctor_get(v___x_949_, 2);
v_auxDeclNGen_954_ = lean_ctor_get(v___x_949_, 3);
v_cache_955_ = lean_ctor_get(v___x_949_, 5);
v_messages_956_ = lean_ctor_get(v___x_949_, 6);
v_infoState_957_ = lean_ctor_get(v___x_949_, 7);
v_snapshotTasks_958_ = lean_ctor_get(v___x_949_, 8);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_988_ == 0)
{
v___x_960_ = v___x_949_;
v_isShared_961_ = v_isSharedCheck_988_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snapshotTasks_958_);
lean_inc(v_infoState_957_);
lean_inc(v_messages_956_);
lean_inc(v_cache_955_);
lean_inc(v_traceState_950_);
lean_inc(v_auxDeclNGen_954_);
lean_inc(v_ngen_953_);
lean_inc(v_nextMacroScope_952_);
lean_inc(v_env_951_);
lean_dec(v___x_949_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_988_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint64_t v_tid_962_; lean_object* v_traces_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_987_; 
v_tid_962_ = lean_ctor_get_uint64(v_traceState_950_, sizeof(void*)*1);
v_traces_963_ = lean_ctor_get(v_traceState_950_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_traceState_950_);
if (v_isSharedCheck_987_ == 0)
{
v___x_965_ = v_traceState_950_;
v_isShared_966_ = v_isSharedCheck_987_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_traces_963_);
lean_dec(v_traceState_950_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_987_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; double v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_967_ = lean_box(0);
v___x_968_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__0);
v___x_969_ = 0;
v___x_970_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_971_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_971_, 0, v_cls_938_);
lean_ctor_set(v___x_971_, 1, v___x_967_);
lean_ctor_set(v___x_971_, 2, v___x_970_);
lean_ctor_set_float(v___x_971_, sizeof(void*)*3, v___x_968_);
lean_ctor_set_float(v___x_971_, sizeof(void*)*3 + 8, v___x_968_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*3 + 16, v___x_969_);
v___x_972_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__2));
v___x_973_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v_a_945_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
lean_inc(v_ref_943_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_ref_943_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_PersistentArray_push___redArg(v_traces_963_, v___x_974_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_975_);
v___x_977_ = v___x_965_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_975_);
lean_ctor_set_uint64(v_reuseFailAlloc_986_, sizeof(void*)*1, v_tid_962_);
v___x_977_ = v_reuseFailAlloc_986_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v___x_977_);
v___x_979_ = v___x_960_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_env_951_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_nextMacroScope_952_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_ngen_953_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_auxDeclNGen_954_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_985_, 5, v_cache_955_);
lean_ctor_set(v_reuseFailAlloc_985_, 6, v_messages_956_);
lean_ctor_set(v_reuseFailAlloc_985_, 7, v_infoState_957_);
lean_ctor_set(v_reuseFailAlloc_985_, 8, v_snapshotTasks_958_);
v___x_979_ = v_reuseFailAlloc_985_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_980_ = lean_st_ref_set(v___y_941_, v___x_979_);
v___x_981_ = lean_box(0);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_981_);
v___x_983_ = v___x_947_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_cls_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_990_, v_msg_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_keys_996_, lean_object* v_i_997_, lean_object* v_k_998_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_array_get_size(v_keys_996_);
v___x_1000_ = lean_nat_dec_lt(v_i_997_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec(v_i_997_);
return v___x_1000_;
}
else
{
lean_object* v_k_x27_1001_; uint8_t v___x_1002_; 
v_k_x27_1001_ = lean_array_fget_borrowed(v_keys_996_, v_i_997_);
v___x_1002_ = l_Lean_instBEqExtraModUse_beq(v_k_998_, v_k_x27_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_i_997_, v___x_1003_);
lean_dec(v_i_997_);
v_i_997_ = v___x_1004_;
goto _start;
}
else
{
lean_dec(v_i_997_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg___boxed(lean_object* v_keys_1006_, lean_object* v_i_1007_, lean_object* v_k_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1006_, v_i_1007_, v_k_1008_);
lean_dec_ref(v_k_1008_);
lean_dec_ref(v_keys_1006_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_x_1011_, size_t v_x_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v_es_1014_; lean_object* v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v_j_1019_; lean_object* v___x_1020_; 
v_es_1014_ = lean_ctor_get(v_x_1011_, 0);
v___x_1015_ = lean_box(2);
v___x_1016_ = ((size_t)5ULL);
v___x_1017_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1_spec__2___redArg___closed__1);
v___x_1018_ = lean_usize_land(v_x_1012_, v___x_1017_);
v_j_1019_ = lean_usize_to_nat(v___x_1018_);
v___x_1020_ = lean_array_get_borrowed(v___x_1015_, v_es_1014_, v_j_1019_);
lean_dec(v_j_1019_);
switch(lean_obj_tag(v___x_1020_))
{
case 0:
{
lean_object* v_key_1021_; uint8_t v___x_1022_; 
v_key_1021_ = lean_ctor_get(v___x_1020_, 0);
v___x_1022_ = l_Lean_instBEqExtraModUse_beq(v_x_1013_, v_key_1021_);
return v___x_1022_;
}
case 1:
{
lean_object* v_node_1023_; size_t v___x_1024_; 
v_node_1023_ = lean_ctor_get(v___x_1020_, 0);
v___x_1024_ = lean_usize_shift_right(v_x_1012_, v___x_1016_);
v_x_1011_ = v_node_1023_;
v_x_1012_ = v___x_1024_;
goto _start;
}
default: 
{
uint8_t v___x_1026_; 
v___x_1026_ = 0;
return v___x_1026_;
}
}
}
else
{
lean_object* v_ks_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_ks_1027_ = lean_ctor_get(v_x_1011_, 0);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_ks_1027_, v___x_1028_, v_x_1013_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
size_t v_x_12210__boxed_1033_; uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_x_12210__boxed_1033_ = lean_unbox_usize(v_x_1031_);
lean_dec(v_x_1031_);
v_res_1034_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1030_, v_x_12210__boxed_1033_, v_x_1032_);
lean_dec_ref(v_x_1032_);
lean_dec_ref(v_x_1030_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
uint64_t v___x_1038_; size_t v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = l_Lean_instHashableExtraModUse_hash(v_x_1037_);
v___x_1039_ = lean_uint64_to_usize(v___x_1038_);
v___x_1040_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1036_, v___x_1039_, v_x_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1041_, v_x_1042_);
lean_dec_ref(v_x_1042_);
lean_dec_ref(v_x_1041_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__1));
v___x_1048_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__0));
v___x_1049_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1048_, v___x_1047_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__3);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__4);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__8));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__10));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15(void){
_start:
{
lean_object* v_cls_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_cls_1069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__14));
v___x_1071_ = l_Lean_Name_append(v___x_1070_, v_cls_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__16));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__18));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_mod_1082_, uint8_t v_isMeta_1083_, lean_object* v_hint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v_env_1089_; uint8_t v_isExporting_1090_; lean_object* v___x_1091_; lean_object* v_env_1092_; lean_object* v___x_1093_; lean_object* v_entry_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1088_ = lean_st_ref_get(v___y_1086_);
v_env_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_env_1089_);
lean_dec(v___x_1088_);
v_isExporting_1090_ = lean_ctor_get_uint8(v_env_1089_, sizeof(void*)*8);
lean_dec_ref(v_env_1089_);
v___x_1091_ = lean_st_ref_get(v___y_1086_);
v_env_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_env_1092_);
lean_dec(v___x_1091_);
v___x_1093_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__2);
lean_inc(v_mod_1082_);
v_entry_1094_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1094_, 0, v_mod_1082_);
lean_ctor_set_uint8(v_entry_1094_, sizeof(void*)*1, v_isExporting_1090_);
lean_ctor_set_uint8(v_entry_1094_, sizeof(void*)*1 + 1, v_isMeta_1083_);
v___x_1095_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1096_ = lean_box(1);
v___x_1097_ = lean_box(0);
v___x_1124_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1093_, v___x_1095_, v_env_1092_, v___x_1096_, v___x_1097_);
v___x_1125_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_1124_, v_entry_1094_);
lean_dec(v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v_options_1126_; uint8_t v_hasTrace_1127_; 
v_options_1126_ = lean_ctor_get(v___y_1085_, 2);
v_hasTrace_1127_ = lean_ctor_get_uint8(v_options_1126_, sizeof(void*)*1);
if (v_hasTrace_1127_ == 0)
{
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___y_1099_ = v___y_1086_;
goto v___jp_1098_;
}
else
{
lean_object* v_inheritedTraceOptions_1128_; lean_object* v_cls_1129_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_inheritedTraceOptions_1128_ = lean_ctor_get(v___y_1085_, 13);
v_cls_1129_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__7));
v___x_1149_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__15);
v___x_1150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1128_, v_options_1126_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___y_1099_ = v___y_1086_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1151_; lean_object* v___y_1153_; 
v___x_1151_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__17);
if (v_isExporting_1090_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__22));
v___y_1153_ = v___x_1160_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__23));
v___y_1153_ = v___x_1161_;
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v___y_1153_);
v___x_1154_ = l_Lean_stringToMessageData(v___y_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
if (v_isMeta_1083_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__20));
v___y_1136_ = v___x_1157_;
v___y_1137_ = v___x_1158_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__21));
v___y_1136_ = v___x_1157_;
v___y_1137_ = v___x_1159_;
goto v___jp_1135_;
}
}
}
v___jp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1131_);
lean_ctor_set(v___x_1133_, 1, v___y_1132_);
v___x_1134_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_cls_1129_, v___x_1133_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec_ref(v___x_1134_);
v___y_1099_ = v___y_1086_;
goto v___jp_1098_;
}
else
{
lean_dec_ref(v_entry_1094_);
return v___x_1134_;
}
}
v___jp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
lean_inc_ref(v___y_1137_);
v___x_1138_ = l_Lean_stringToMessageData(v___y_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1136_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__9);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_MessageData_ofName(v_mod_1082_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_Name_isAnonymous(v_hint_1084_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__11);
v___x_1146_ = l_Lean_MessageData_ofName(v_hint_1084_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___y_1131_ = v___x_1143_;
v___y_1132_ = v___x_1147_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_hint_1084_);
v___x_1148_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__12);
v___y_1131_ = v___x_1143_;
v___y_1132_ = v___x_1148_;
goto v___jp_1130_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec_ref(v_entry_1094_);
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
v___jp_1098_:
{
lean_object* v___x_1100_; lean_object* v_toEnvExtension_1101_; lean_object* v_env_1102_; lean_object* v_nextMacroScope_1103_; lean_object* v_ngen_1104_; lean_object* v_auxDeclNGen_1105_; lean_object* v_traceState_1106_; lean_object* v_messages_1107_; lean_object* v_infoState_1108_; lean_object* v_snapshotTasks_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1122_; 
v___x_1100_ = lean_st_ref_take(v___y_1099_);
v_toEnvExtension_1101_ = lean_ctor_get(v___x_1095_, 0);
v_env_1102_ = lean_ctor_get(v___x_1100_, 0);
v_nextMacroScope_1103_ = lean_ctor_get(v___x_1100_, 1);
v_ngen_1104_ = lean_ctor_get(v___x_1100_, 2);
v_auxDeclNGen_1105_ = lean_ctor_get(v___x_1100_, 3);
v_traceState_1106_ = lean_ctor_get(v___x_1100_, 4);
v_messages_1107_ = lean_ctor_get(v___x_1100_, 6);
v_infoState_1108_ = lean_ctor_get(v___x_1100_, 7);
v_snapshotTasks_1109_ = lean_ctor_get(v___x_1100_, 8);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1100_, 5);
lean_dec(v_unused_1123_);
v___x_1111_ = v___x_1100_;
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snapshotTasks_1109_);
lean_inc(v_infoState_1108_);
lean_inc(v_messages_1107_);
lean_inc(v_traceState_1106_);
lean_inc(v_auxDeclNGen_1105_);
lean_inc(v_ngen_1104_);
lean_inc(v_nextMacroScope_1103_);
lean_inc(v_env_1102_);
lean_dec(v___x_1100_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_asyncMode_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_asyncMode_1113_ = lean_ctor_get(v_toEnvExtension_1101_, 2);
v___x_1114_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1095_, v_env_1102_, v_entry_1094_, v_asyncMode_1113_, v___x_1097_);
v___x_1115_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 5, v___x_1115_);
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1117_ = v___x_1111_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_nextMacroScope_1103_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_ngen_1104_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_auxDeclNGen_1105_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_traceState_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1121_, 6, v_messages_1107_);
lean_ctor_set(v_reuseFailAlloc_1121_, 7, v_infoState_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 8, v_snapshotTasks_1109_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_st_ref_set(v___y_1099_, v___x_1117_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_mod_1164_, lean_object* v_isMeta_1165_, lean_object* v_hint_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_isMeta_boxed_1170_; lean_object* v_res_1171_; 
v_isMeta_boxed_1170_ = lean_unbox(v_isMeta_1165_);
v_res_1171_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_mod_1164_, v_isMeta_boxed_1170_, v_hint_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(lean_object* v___x_1172_, lean_object* v_declName_1173_, lean_object* v_as_1174_, size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1176_, v_sz_1175_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_declName_1173_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_b_1177_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v_modules_1184_; lean_object* v___x_1185_; lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v_toImport_1188_; lean_object* v_module_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1183_ = l_Lean_Environment_header(v___x_1172_);
v_modules_1184_ = lean_ctor_get(v___x_1183_, 3);
lean_inc_ref(v_modules_1184_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1186_ = lean_array_uget_borrowed(v_as_1174_, v_i_1176_);
v___x_1187_ = lean_array_get(v___x_1185_, v_modules_1184_, v_a_1186_);
lean_dec_ref(v_modules_1184_);
v_toImport_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_toImport_1188_);
lean_dec(v___x_1187_);
v_module_1189_ = lean_ctor_get(v_toImport_1188_, 0);
lean_inc(v_module_1189_);
lean_dec_ref(v_toImport_1188_);
v___x_1190_ = 0;
lean_inc(v_declName_1173_);
v___x_1191_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1189_, v___x_1190_, v_declName_1173_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; 
lean_dec_ref(v___x_1191_);
v___x_1192_ = lean_box(0);
v___x_1193_ = ((size_t)1ULL);
v___x_1194_ = lean_usize_add(v_i_1176_, v___x_1193_);
v_i_1176_ = v___x_1194_;
v_b_1177_ = v___x_1192_;
goto _start;
}
else
{
lean_dec(v_declName_1173_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7___boxed(lean_object* v___x_1196_, lean_object* v_declName_1197_, lean_object* v_as_1198_, lean_object* v_sz_1199_, lean_object* v_i_1200_, lean_object* v_b_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v___x_1196_, v_declName_1197_, v_as_1198_, v_sz_boxed_1205_, v_i_boxed_1206_, v_b_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_as_1198_);
lean_dec_ref(v___x_1196_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(lean_object* v_a_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_box(0);
return v___x_1210_;
}
else
{
lean_object* v_key_1211_; lean_object* v_value_1212_; lean_object* v_tail_1213_; uint8_t v___x_1214_; 
v_key_1211_ = lean_ctor_get(v_x_1209_, 0);
v_value_1212_ = lean_ctor_get(v_x_1209_, 1);
v_tail_1213_ = lean_ctor_get(v_x_1209_, 2);
v___x_1214_ = lean_name_eq(v_key_1211_, v_a_1208_);
if (v___x_1214_ == 0)
{
v_x_1209_ = v_tail_1213_;
goto _start;
}
else
{
lean_object* v___x_1216_; 
lean_inc(v_value_1212_);
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_value_1212_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_a_1217_, lean_object* v_x_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1217_, v_x_1218_);
lean_dec(v_x_1218_);
lean_dec(v_a_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(lean_object* v_m_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_buckets_1222_; lean_object* v___x_1223_; uint64_t v___y_1225_; 
v_buckets_1222_ = lean_ctor_get(v_m_1220_, 1);
v___x_1223_ = lean_array_get_size(v_buckets_1222_);
if (lean_obj_tag(v_a_1221_) == 0)
{
uint64_t v___x_1239_; 
v___x_1239_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Parser_Tactic_Doc_isTactic_spec__1___redArg___closed__0);
v___y_1225_ = v___x_1239_;
goto v___jp_1224_;
}
else
{
uint64_t v_hash_1240_; 
v_hash_1240_ = lean_ctor_get_uint64(v_a_1221_, sizeof(void*)*2);
v___y_1225_ = v_hash_1240_;
goto v___jp_1224_;
}
v___jp_1224_:
{
uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v_fold_1228_; uint64_t v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1226_ = 32ULL;
v___x_1227_ = lean_uint64_shift_right(v___y_1225_, v___x_1226_);
v_fold_1228_ = lean_uint64_xor(v___y_1225_, v___x_1227_);
v___x_1229_ = 16ULL;
v___x_1230_ = lean_uint64_shift_right(v_fold_1228_, v___x_1229_);
v___x_1231_ = lean_uint64_xor(v_fold_1228_, v___x_1230_);
v___x_1232_ = lean_uint64_to_usize(v___x_1231_);
v___x_1233_ = lean_usize_of_nat(v___x_1223_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_sub(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_usize_land(v___x_1232_, v___x_1235_);
v___x_1237_ = lean_array_uget_borrowed(v_buckets_1222_, v___x_1236_);
v___x_1238_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1221_, v___x_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg___boxed(lean_object* v_m_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_m_1241_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__1));
v___x_1247_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__0));
v___x_1248_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1247_, v___x_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(lean_object* v_declName_1251_, uint8_t v_isMeta_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v_env_1260_; lean_object* v___y_1262_; lean_object* v___x_1275_; 
v___x_1256_ = lean_st_ref_get(v___y_1254_);
v_env_1260_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1256_);
v___x_1275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1260_, v_declName_1251_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
goto v___jp_1257_;
}
else
{
lean_object* v_val_1276_; lean_object* v___x_1277_; lean_object* v_modules_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_Environment_header(v_env_1260_);
v_modules_1278_ = lean_ctor_get(v___x_1277_, 3);
lean_inc_ref(v_modules_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_array_get_size(v_modules_1278_);
v___x_1280_ = lean_nat_dec_lt(v_val_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_modules_1278_);
lean_dec(v_val_1276_);
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
goto v___jp_1257_;
}
else
{
lean_object* v___x_1281_; lean_object* v_env_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___y_1286_; 
v___x_1281_ = lean_st_ref_get(v___y_1254_);
v_env_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_env_1282_);
lean_dec(v___x_1281_);
v___x_1283_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__2);
v___x_1284_ = lean_array_fget(v_modules_1278_, v_val_1276_);
lean_dec(v_val_1276_);
lean_dec_ref(v_modules_1278_);
if (v_isMeta_1252_ == 0)
{
lean_dec_ref(v_env_1282_);
v___y_1286_ = v_isMeta_1252_;
goto v___jp_1285_;
}
else
{
uint8_t v___x_1297_; 
lean_inc(v_declName_1251_);
v___x_1297_ = l_Lean_isMarkedMeta(v_env_1282_, v_declName_1251_);
if (v___x_1297_ == 0)
{
v___y_1286_ = v_isMeta_1252_;
goto v___jp_1285_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = 0;
v___y_1286_ = v___x_1298_;
goto v___jp_1285_;
}
}
v___jp_1285_:
{
lean_object* v_toImport_1287_; lean_object* v_module_1288_; lean_object* v___x_1289_; 
v_toImport_1287_ = lean_ctor_get(v___x_1284_, 0);
lean_inc_ref(v_toImport_1287_);
lean_dec(v___x_1284_);
v_module_1288_ = lean_ctor_get(v_toImport_1287_, 0);
lean_inc(v_module_1288_);
lean_dec_ref(v_toImport_1287_);
lean_inc(v_declName_1251_);
v___x_1289_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6(v_module_1288_, v___y_1286_, v_declName_1251_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v___x_1289_);
v___x_1290_ = l_Lean_indirectModUseExt;
v___x_1291_ = lean_box(1);
v___x_1292_ = lean_box(0);
lean_inc_ref(v_env_1260_);
v___x_1293_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1283_, v___x_1290_, v_env_1260_, v___x_1291_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v___x_1293_, v_declName_1251_);
lean_dec(v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___closed__3));
v___y_1262_ = v___x_1295_;
goto v___jp_1261_;
}
else
{
lean_object* v_val_1296_; 
v_val_1296_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1296_);
lean_dec_ref(v___x_1294_);
v___y_1262_ = v_val_1296_;
goto v___jp_1261_;
}
}
else
{
lean_dec_ref(v_env_1260_);
lean_dec(v_declName_1251_);
return v___x_1289_;
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v_sz_1264_ = lean_array_size(v___y_1262_);
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__7(v_env_1260_, v_declName_1251_, v___y_1262_, v_sz_1264_, v___x_1265_, v___x_1263_, v___y_1253_, v___y_1254_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v_env_1260_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1274_);
v___x_1268_ = v___x_1266_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1263_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1263_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4___boxed(lean_object* v_declName_1299_, lean_object* v_isMeta_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_isMeta_boxed_1304_; lean_object* v_res_1305_; 
v_isMeta_boxed_1304_ = lean_unbox(v_isMeta_1300_);
v_res_1305_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_declName_1299_, v_isMeta_boxed_1304_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(lean_object* v_ref_1306_, lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_fileName_1311_; lean_object* v_fileMap_1312_; lean_object* v_options_1313_; lean_object* v_currRecDepth_1314_; lean_object* v_maxRecDepth_1315_; lean_object* v_ref_1316_; lean_object* v_currNamespace_1317_; lean_object* v_openDecls_1318_; lean_object* v_initHeartbeats_1319_; lean_object* v_maxHeartbeats_1320_; lean_object* v_quotContext_1321_; lean_object* v_currMacroScope_1322_; uint8_t v_diag_1323_; lean_object* v_cancelTk_x3f_1324_; uint8_t v_suppressElabErrors_1325_; lean_object* v_inheritedTraceOptions_1326_; lean_object* v_ref_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_fileName_1311_ = lean_ctor_get(v___y_1308_, 0);
v_fileMap_1312_ = lean_ctor_get(v___y_1308_, 1);
v_options_1313_ = lean_ctor_get(v___y_1308_, 2);
v_currRecDepth_1314_ = lean_ctor_get(v___y_1308_, 3);
v_maxRecDepth_1315_ = lean_ctor_get(v___y_1308_, 4);
v_ref_1316_ = lean_ctor_get(v___y_1308_, 5);
v_currNamespace_1317_ = lean_ctor_get(v___y_1308_, 6);
v_openDecls_1318_ = lean_ctor_get(v___y_1308_, 7);
v_initHeartbeats_1319_ = lean_ctor_get(v___y_1308_, 8);
v_maxHeartbeats_1320_ = lean_ctor_get(v___y_1308_, 9);
v_quotContext_1321_ = lean_ctor_get(v___y_1308_, 10);
v_currMacroScope_1322_ = lean_ctor_get(v___y_1308_, 11);
v_diag_1323_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*14);
v_cancelTk_x3f_1324_ = lean_ctor_get(v___y_1308_, 12);
v_suppressElabErrors_1325_ = lean_ctor_get_uint8(v___y_1308_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1326_ = lean_ctor_get(v___y_1308_, 13);
v_ref_1327_ = l_Lean_replaceRef(v_ref_1306_, v_ref_1316_);
lean_inc_ref(v_inheritedTraceOptions_1326_);
lean_inc(v_cancelTk_x3f_1324_);
lean_inc(v_currMacroScope_1322_);
lean_inc(v_quotContext_1321_);
lean_inc(v_maxHeartbeats_1320_);
lean_inc(v_initHeartbeats_1319_);
lean_inc(v_openDecls_1318_);
lean_inc(v_currNamespace_1317_);
lean_inc(v_maxRecDepth_1315_);
lean_inc(v_currRecDepth_1314_);
lean_inc_ref(v_options_1313_);
lean_inc_ref(v_fileMap_1312_);
lean_inc_ref(v_fileName_1311_);
v___x_1328_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1328_, 0, v_fileName_1311_);
lean_ctor_set(v___x_1328_, 1, v_fileMap_1312_);
lean_ctor_set(v___x_1328_, 2, v_options_1313_);
lean_ctor_set(v___x_1328_, 3, v_currRecDepth_1314_);
lean_ctor_set(v___x_1328_, 4, v_maxRecDepth_1315_);
lean_ctor_set(v___x_1328_, 5, v_ref_1327_);
lean_ctor_set(v___x_1328_, 6, v_currNamespace_1317_);
lean_ctor_set(v___x_1328_, 7, v_openDecls_1318_);
lean_ctor_set(v___x_1328_, 8, v_initHeartbeats_1319_);
lean_ctor_set(v___x_1328_, 9, v_maxHeartbeats_1320_);
lean_ctor_set(v___x_1328_, 10, v_quotContext_1321_);
lean_ctor_set(v___x_1328_, 11, v_currMacroScope_1322_);
lean_ctor_set(v___x_1328_, 12, v_cancelTk_x3f_1324_);
lean_ctor_set(v___x_1328_, 13, v_inheritedTraceOptions_1326_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*14, v_diag_1323_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*14 + 1, v_suppressElabErrors_1325_);
v___x_1329_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1307_, v___x_1328_, v___y_1309_);
lean_dec_ref(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_ref_1330_, lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1330_, v_msg_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v_ref_1330_);
return v_res_1335_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__0));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__2));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__4));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(lean_object* v_attrName_1345_, lean_object* v_declName_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1350_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__1);
v___x_1351_ = l_Lean_MessageData_ofName(v_attrName_1345_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__3);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = 0;
v___x_1356_ = l_Lean_MessageData_ofConstName(v_declName_1346_, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1354_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___closed__5);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1359_, v___y_1347_, v___y_1348_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg___boxed(lean_object* v_attrName_1361_, lean_object* v_declName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1361_, v_declName_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(uint8_t v___y_1367_, lean_object* v_as_1368_, size_t v_i_1369_, size_t v_stop_1370_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_eq(v_i_1369_, v_stop_1370_);
if (v___x_1371_ == 0)
{
uint8_t v___x_1372_; uint8_t v___y_1374_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1372_ = 1;
v___x_1378_ = lean_array_uget_borrowed(v_as_1368_, v_i_1369_);
v___x_1379_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_1380_ = lean_name_eq(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
v___y_1374_ = v___x_1371_;
goto v___jp_1373_;
}
else
{
if (v___x_1371_ == 0)
{
v___y_1374_ = v___y_1367_;
goto v___jp_1373_;
}
else
{
v___y_1374_ = v___x_1371_;
goto v___jp_1373_;
}
}
v___jp_1373_:
{
if (v___y_1374_ == 0)
{
size_t v___x_1375_; size_t v___x_1376_; 
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1369_, v___x_1375_);
v_i_1369_ = v___x_1376_;
goto _start;
}
else
{
return v___x_1372_;
}
}
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3___boxed(lean_object* v___y_1382_, lean_object* v_as_1383_, lean_object* v_i_1384_, lean_object* v_stop_1385_){
_start:
{
uint8_t v___y_12780__boxed_1386_; size_t v_i_boxed_1387_; size_t v_stop_boxed_1388_; uint8_t v_res_1389_; lean_object* v_r_1390_; 
v___y_12780__boxed_1386_ = lean_unbox(v___y_1382_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_stop_boxed_1388_ = lean_unbox_usize(v_stop_1385_);
lean_dec(v_stop_1385_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_12780__boxed_1386_, v_as_1383_, v_i_boxed_1387_, v_stop_boxed_1388_);
lean_dec_ref(v_as_1383_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__0_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1393_ = l_Lean_stringToMessageData(v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__4_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1399_ = l_Lean_stringToMessageData(v___x_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__6_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__8_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__11_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1409_ = l_Lean_stringToMessageData(v___x_1408_);
return v___x_1409_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__13_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1412_ = l_Lean_stringToMessageData(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__15_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_name_1421_, lean_object* v_decl_1422_, lean_object* v_stx_1423_, uint8_t v_kind_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___f_1507_; lean_object* v___y_1509_; lean_object* v___y_1510_; uint8_t v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1541_; lean_object* v___y_1542_; uint8_t v___x_1581_; uint8_t v___x_1582_; 
lean_inc(v_decl_1422_);
v___f_1507_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed), 6, 1);
lean_closure_set(v___f_1507_, 0, v_decl_1422_);
v___x_1581_ = 0;
v___x_1582_ = l_Lean_instBEqAttributeKind_beq(v_kind_1424_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___f_1507_);
lean_dec(v_stx_1423_);
lean_dec(v_decl_1422_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v___x_1418_);
lean_dec(v___x_1416_);
v___x_1583_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1421_, v_kind_1424_, v___y_1425_, v___y_1426_);
return v___x_1583_;
}
else
{
goto v___jp_1576_;
}
v___jp_1428_:
{
lean_object* v___x_1431_; lean_object* v_env_1432_; lean_object* v_nextMacroScope_1433_; lean_object* v_ngen_1434_; lean_object* v_auxDeclNGen_1435_; lean_object* v_traceState_1436_; lean_object* v_messages_1437_; lean_object* v_infoState_1438_; lean_object* v_snapshotTasks_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1455_; 
v___x_1431_ = lean_st_ref_take(v___y_1430_);
v_env_1432_ = lean_ctor_get(v___x_1431_, 0);
v_nextMacroScope_1433_ = lean_ctor_get(v___x_1431_, 1);
v_ngen_1434_ = lean_ctor_get(v___x_1431_, 2);
v_auxDeclNGen_1435_ = lean_ctor_get(v___x_1431_, 3);
v_traceState_1436_ = lean_ctor_get(v___x_1431_, 4);
v_messages_1437_ = lean_ctor_get(v___x_1431_, 6);
v_infoState_1438_ = lean_ctor_get(v___x_1431_, 7);
v_snapshotTasks_1439_ = lean_ctor_get(v___x_1431_, 8);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1431_, 5);
lean_dec(v_unused_1456_);
v___x_1441_ = v___x_1431_;
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_snapshotTasks_1439_);
lean_inc(v_infoState_1438_);
lean_inc(v_messages_1437_);
lean_inc(v_traceState_1436_);
lean_inc(v_auxDeclNGen_1435_);
lean_inc(v_ngen_1434_);
lean_inc(v_nextMacroScope_1433_);
lean_inc(v_env_1432_);
lean_dec(v___x_1431_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v_toEnvExtension_1444_; lean_object* v_asyncMode_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1443_ = l_Lean_Parser_Tactic_Doc_tacticAlternativeExt;
v_toEnvExtension_1444_ = lean_ctor_get(v___x_1443_, 0);
v_asyncMode_1445_ = lean_ctor_get(v_toEnvExtension_1444_, 2);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_decl_1422_);
lean_ctor_set(v___x_1446_, 1, v___y_1429_);
v___x_1447_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1443_, v_env_1432_, v___x_1446_, v_asyncMode_1445_, v___x_1416_);
v___x_1448_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 5, v___x_1448_);
lean_ctor_set(v___x_1441_, 0, v___x_1447_);
v___x_1450_ = v___x_1441_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_nextMacroScope_1433_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_ngen_1434_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_auxDeclNGen_1435_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_traceState_1436_);
lean_ctor_set(v_reuseFailAlloc_1454_, 5, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 6, v_messages_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 7, v_infoState_1438_);
lean_ctor_set(v_reuseFailAlloc_1454_, 8, v_snapshotTasks_1439_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_st_ref_set(v___y_1430_, v___x_1450_);
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1461_; lean_object* v_env_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_st_ref_get(v___y_1460_);
v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_env_1462_);
lean_dec(v___x_1461_);
lean_inc(v___y_1458_);
v___x_1463_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1462_, v___y_1458_);
if (lean_obj_tag(v___x_1463_) == 1)
{
lean_object* v_val_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
v_val_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1464_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1466_ = l_Lean_MessageData_ofName(v___y_1458_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_MessageData_ofName(v_val_1464_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1465_);
v___x_1473_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1472_, v___y_1459_, v___y_1460_);
return v___x_1473_;
}
else
{
lean_dec(v___x_1463_);
v___y_1429_ = v___y_1458_;
v___y_1430_ = v___y_1460_;
goto v___jp_1428_;
}
}
v___jp_1474_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v___y_1476_);
v___x_1480_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1481_ = l_Lean_MessageData_ofName(v_decl_1422_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_inc_ref(v___y_1479_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___y_1479_);
v___x_1486_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__19);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_array_to_list(v___y_1477_);
v___x_1489_ = l_Lean_MessageData_andList(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1487_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1492_, v___y_1478_, v___y_1475_);
return v___x_1493_;
}
v___jp_1494_:
{
size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_sz_1500_ = lean_array_size(v___y_1498_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2(v_sz_1500_, v___x_1501_, v___y_1498_);
v___x_1503_ = lean_array_get_size(v___x_1502_);
v___x_1504_ = lean_nat_dec_lt(v___y_1497_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__7_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1475_ = v___y_1495_;
v___y_1476_ = v___y_1496_;
v___y_1477_ = v___x_1502_;
v___y_1478_ = v___y_1499_;
v___y_1479_ = v___x_1505_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__9_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___y_1475_ = v___y_1495_;
v___y_1476_ = v___y_1496_;
v___y_1477_ = v___x_1502_;
v___y_1478_ = v___y_1499_;
v___y_1479_ = v___x_1506_;
goto v___jp_1474_;
}
}
v___jp_1508_:
{
lean_object* v___x_1514_; lean_object* v_env_1515_; lean_object* v___x_1516_; lean_object* v_ext_1517_; lean_object* v_toEnvExtension_1518_; lean_object* v_asyncMode_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_categories_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1514_ = lean_st_ref_get(v___y_1513_);
v_env_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_ref(v_env_1515_);
lean_dec(v___x_1514_);
v___x_1516_ = l_Lean_Parser_parserExtension;
v_ext_1517_ = lean_ctor_get(v___x_1516_, 1);
v_toEnvExtension_1518_ = lean_ctor_get(v_ext_1517_, 0);
v_asyncMode_1519_ = lean_ctor_get(v_toEnvExtension_1518_, 2);
v___x_1520_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1521_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1520_, v___x_1516_, v_env_1515_, v_asyncMode_1519_);
v_categories_1522_ = lean_ctor_get(v___x_1521_, 2);
lean_inc_ref(v_categories_1522_);
lean_dec(v___x_1521_);
v___x_1523_ = lean_mk_empty_array_with_capacity(v___x_1417_);
v___x_1524_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_categories_1522_, v___x_1523_, v___f_1507_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = lean_array_get_size(v_a_1525_);
v___x_1527_ = lean_nat_dec_eq(v___x_1526_, v___x_1417_);
if (v___x_1527_ == 0)
{
if (v___y_1511_ == 0)
{
lean_dec(v_a_1525_);
v___y_1458_ = v___y_1509_;
v___y_1459_ = v___y_1512_;
v___y_1460_ = v___y_1513_;
goto v___jp_1457_;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v___x_1417_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_dec(v___x_1416_);
v___y_1495_ = v___y_1513_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v_a_1525_;
v___y_1499_ = v___y_1512_;
goto v___jp_1494_;
}
else
{
if (v___x_1528_ == 0)
{
lean_dec(v___x_1416_);
v___y_1495_ = v___y_1513_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v_a_1525_;
v___y_1499_ = v___y_1512_;
goto v___jp_1494_;
}
else
{
size_t v___x_1529_; size_t v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = lean_usize_of_nat(v___x_1526_);
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__3(v___y_1511_, v_a_1525_, v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_dec(v___x_1416_);
v___y_1495_ = v___y_1513_;
v___y_1496_ = v___y_1509_;
v___y_1497_ = v___y_1510_;
v___y_1498_ = v_a_1525_;
v___y_1499_ = v___y_1512_;
goto v___jp_1494_;
}
else
{
lean_dec(v_a_1525_);
v___y_1458_ = v___y_1509_;
v___y_1459_ = v___y_1512_;
v___y_1460_ = v___y_1513_;
goto v___jp_1457_;
}
}
}
}
}
else
{
lean_dec(v_a_1525_);
v___y_1458_ = v___y_1509_;
v___y_1459_ = v___y_1512_;
v___y_1460_ = v___y_1513_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v___y_1509_);
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
v_a_1532_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1524_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1524_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
v___jp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1544_ = l_Lean_Name_mkStr4(v___x_1418_, v___x_1419_, v___x_1543_, v___x_1420_);
lean_inc(v_stx_1423_);
v___x_1545_ = l_Lean_Syntax_isOfKind(v_stx_1423_, v___x_1544_);
lean_dec(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v___f_1507_);
lean_dec(v_stx_1423_);
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
v___x_1546_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1547_ = l_Lean_MessageData_ofName(v_name_1421_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_1550_, v___y_1541_, v___y_1542_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_name_1421_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = l_Lean_Syntax_getArg(v_stx_1423_, v___x_1552_);
lean_dec(v_stx_1423_);
v___x_1554_ = lean_box(0);
lean_inc(v___x_1553_);
v___x_1555_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1553_, v___x_1554_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_n(v_a_1556_, 2);
lean_dec_ref(v___x_1555_);
v___x_1557_ = 0;
v___x_1558_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4(v_a_1556_, v___x_1557_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; lean_object* v_env_1560_; uint8_t v___x_1561_; 
lean_dec_ref(v___x_1558_);
v___x_1559_ = lean_st_ref_get(v___y_1542_);
v_env_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc_ref(v_env_1560_);
lean_dec(v___x_1559_);
v___x_1561_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_1560_, v_a_1556_);
if (v___x_1561_ == 0)
{
if (v___x_1545_ == 0)
{
lean_dec(v___x_1553_);
v___y_1509_ = v_a_1556_;
v___y_1510_ = v___x_1552_;
v___y_1511_ = v___x_1545_;
v___y_1512_ = v___y_1541_;
v___y_1513_ = v___y_1542_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v___f_1507_);
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
v___x_1562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_1563_ = l_Lean_MessageData_ofName(v_a_1556_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v___x_1553_, v___x_1566_, v___y_1541_, v___y_1542_);
lean_dec(v___x_1553_);
return v___x_1567_;
}
}
else
{
lean_dec(v___x_1553_);
v___y_1509_ = v_a_1556_;
v___y_1510_ = v___x_1552_;
v___y_1511_ = v___x_1545_;
v___y_1512_ = v___y_1541_;
v___y_1513_ = v___y_1542_;
goto v___jp_1508_;
}
}
else
{
lean_dec(v_a_1556_);
lean_dec(v___x_1553_);
lean_dec_ref(v___f_1507_);
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
return v___x_1558_;
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v___x_1553_);
lean_dec_ref(v___f_1507_);
lean_dec(v_decl_1422_);
lean_dec(v___x_1416_);
v_a_1568_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1555_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1555_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; lean_object* v_env_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_st_ref_get(v___y_1426_);
v_env_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1577_);
v___x_1579_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1578_, v_decl_1422_);
lean_dec_ref(v_env_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
v___y_1541_ = v___y_1425_;
v___y_1542_ = v___y_1426_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1580_; 
lean_dec_ref(v___x_1579_);
lean_dec_ref(v___f_1507_);
lean_dec(v_stx_1423_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v___x_1418_);
lean_dec(v___x_1416_);
v___x_1580_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_name_1421_, v_decl_1422_, v___y_1425_, v___y_1426_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v___x_1588_, lean_object* v_name_1589_, lean_object* v_decl_1590_, lean_object* v_stx_1591_, lean_object* v_kind_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v_kind_boxed_1596_; lean_object* v_res_1597_; 
v_kind_boxed_1596_ = lean_unbox(v_kind_1592_);
v_res_1597_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(v___x_1584_, v___x_1585_, v___x_1586_, v___x_1587_, v___x_1588_, v_name_1589_, v_decl_1590_, v_stx_1591_, v_kind_boxed_1596_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___x_1585_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__31_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_1687_ = l_Lean_registerBuiltinAttribute(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2____boxed(lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1690_, lean_object* v_msg_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v_msg_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0(v_00_u03b1_1696_, v_msg_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(lean_object* v_00_u03c3_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_map_1704_, lean_object* v_init_1705_, lean_object* v_f_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___redArg(v_map_1704_, v_init_1705_, v_f_1706_, v___y_1707_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03c3_1711_, lean_object* v_00_u03b2_1712_, lean_object* v_map_1713_, lean_object* v_init_1714_, lean_object* v_f_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1(v_00_u03c3_1711_, v_00_u03b2_1712_, v_map_1713_, v_init_1714_, v_f_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1720_, lean_object* v_ref_1721_, lean_object* v_msg_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_ref_1721_, v_msg_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_ref_1728_, lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5(v_00_u03b1_1727_, v_ref_1728_, v_msg_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v_ref_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(lean_object* v_00_u03b1_1734_, lean_object* v_attrName_1735_, lean_object* v_declName_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___redArg(v_attrName_1735_, v_declName_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_attrName_1742_, lean_object* v_declName_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__6(v_00_u03b1_1741_, v_attrName_1742_, v_declName_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(lean_object* v_00_u03b1_1748_, lean_object* v_name_1749_, uint8_t v_kind_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_1749_, v_kind_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_name_1756_, lean_object* v_kind_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v_kind_boxed_1761_; lean_object* v_res_1762_; 
v_kind_boxed_1761_ = lean_unbox(v_kind_1757_);
v_res_1762_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7(v_00_u03b1_1755_, v_name_1756_, v_kind_boxed_1761_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_1763_, lean_object* v_f_1764_, lean_object* v_init_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1764_, v_map_1763_, v_init_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_1770_, lean_object* v_f_1771_, lean_object* v_init_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_1770_, v_f_1771_, v_init_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_1777_, lean_object* v_00_u03c3_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_map_1780_, lean_object* v_f_1781_, lean_object* v_init_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1781_, v_map_1780_, v_init_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_1787_, lean_object* v_00_u03c3_1788_, lean_object* v_00_u03b2_1789_, lean_object* v_map_1790_, lean_object* v_f_1791_, lean_object* v_init_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_1787_, v_00_u03c3_1788_, v_00_u03b2_1789_, v_map_1790_, v_f_1791_, v_init_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(lean_object* v_00_u03b2_1797_, lean_object* v_m_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___redArg(v_m_1798_, v_a_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8___boxed(lean_object* v_00_u03b2_1801_, lean_object* v_m_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8(v_00_u03b2_1801_, v_m_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_m_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1805_, lean_object* v_00_u03c3_1806_, lean_object* v_00_u03b1_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_f_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_f_1809_, v_x_1810_, v_x_1811_, v___y_1812_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1816_, lean_object* v_00_u03c3_1817_, lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_f_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03c3_1816_, v_00_u03c3_1817_, v_00_u03b1_1818_, v_00_u03b2_1819_, v_f_1820_, v_x_1821_, v_x_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_x_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8(v_00_u03b2_1831_, v_x_1832_, v_x_1833_);
lean_dec_ref(v_x_1833_);
lean_dec_ref(v_x_1832_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1836_, lean_object* v_a_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___redArg(v_a_1837_, v_x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1840_, lean_object* v_a_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__8_spec__12(v_00_u03b2_1840_, v_a_1841_, v_x_1842_);
lean_dec(v_x_1842_);
lean_dec(v_a_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_00_u03c3_1846_, lean_object* v_00_u03c3_1847_, lean_object* v_f_1848_, lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___redArg(v_f_1848_, v_as_1849_, v_i_1850_, v_stop_1851_, v_b_1852_, v___y_1853_, v___y_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_00_u03c3_1859_, lean_object* v_00_u03c3_1860_, lean_object* v_f_1861_, lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_stop_1864_, lean_object* v_b_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
size_t v_i_boxed_1869_; size_t v_stop_boxed_1870_; lean_object* v_res_1871_; 
v_i_boxed_1869_ = lean_unbox_usize(v_i_1863_);
lean_dec(v_i_1863_);
v_stop_boxed_1870_ = lean_unbox_usize(v_stop_1864_);
lean_dec(v_stop_1864_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__10(v_00_u03b1_1857_, v_00_u03b2_1858_, v_00_u03c3_1859_, v_00_u03c3_1860_, v_f_1861_, v_as_1862_, v_i_boxed_1869_, v_stop_boxed_1870_, v_b_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_as_1862_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(lean_object* v_00_u03c3_1872_, lean_object* v_00_u03c3_1873_, lean_object* v_00_u03b1_1874_, lean_object* v_00_u03b2_1875_, lean_object* v_f_1876_, lean_object* v_keys_1877_, lean_object* v_vals_1878_, lean_object* v_heq_1879_, lean_object* v_i_1880_, lean_object* v_acc_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___redArg(v_f_1876_, v_keys_1877_, v_vals_1878_, v_i_1880_, v_acc_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03c3_1886_, lean_object* v_00_u03c3_1887_, lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_f_1890_, lean_object* v_keys_1891_, lean_object* v_vals_1892_, lean_object* v_heq_1893_, lean_object* v_i_1894_, lean_object* v_acc_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__11(v_00_u03c3_1886_, v_00_u03c3_1887_, v_00_u03b1_1888_, v_00_u03b2_1889_, v_f_1890_, v_keys_1891_, v_vals_1892_, v_heq_1893_, v_i_1894_, v_acc_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_vals_1892_);
lean_dec_ref(v_keys_1891_);
return v_res_1899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1900_, lean_object* v_x_1901_, size_t v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___redArg(v_x_1901_, v_x_1902_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
size_t v_x_13602__boxed_1909_; uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_x_13602__boxed_1909_ = lean_unbox_usize(v_x_1907_);
lean_dec(v_x_1907_);
v_res_1910_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14(v_00_u03b2_1905_, v_x_1906_, v_x_13602__boxed_1909_, v_x_1908_);
lean_dec_ref(v_x_1908_);
lean_dec_ref(v_x_1906_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(lean_object* v_00_u03b2_1912_, lean_object* v_keys_1913_, lean_object* v_vals_1914_, lean_object* v_heq_1915_, lean_object* v_i_1916_, lean_object* v_k_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___redArg(v_keys_1913_, v_i_1916_, v_k_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v_00_u03b2_1919_, lean_object* v_keys_1920_, lean_object* v_vals_1921_, lean_object* v_heq_1922_, lean_object* v_i_1923_, lean_object* v_k_1924_){
_start:
{
uint8_t v_res_1925_; lean_object* v_r_1926_; 
v_res_1925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__14_spec__17(v_00_u03b2_1919_, v_keys_1920_, v_vals_1921_, v_heq_1922_, v_i_1923_, v_k_1924_);
lean_dec_ref(v_k_1924_);
lean_dec_ref(v_vals_1921_);
lean_dec_ref(v_keys_1920_);
v_r_1926_ = lean_box(v_res_1925_);
return v_r_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_as_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1931_; 
v_fst_1929_ = lean_ctor_get(v_x_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_x_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec_ref(v_x_1928_);
v___x_1931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1929_, v_snd_1930_, v_as_1927_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_k_1934_; lean_object* v_v_1935_; lean_object* v_l_1936_; lean_object* v_r_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_k_1934_ = lean_ctor_get(v_x_1933_, 1);
v_v_1935_ = lean_ctor_get(v_x_1933_, 2);
v_l_1936_ = lean_ctor_get(v_x_1933_, 3);
v_r_1937_ = lean_ctor_get(v_x_1933_, 4);
v___x_1938_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1932_, v_l_1936_);
lean_inc(v_v_1935_);
lean_inc(v_k_1934_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_k_1934_);
lean_ctor_set(v___x_1939_, 1, v_v_1935_);
v___x_1940_ = lean_array_push(v___x_1938_, v___x_1939_);
v_init_1932_ = v___x_1940_;
v_x_1933_ = v_r_1937_;
goto _start;
}
else
{
return v_init_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_1942_, lean_object* v_x_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_1942_, v_x_1943_);
lean_dec(v_x_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_1945_, lean_object* v_x2_1946_){
_start:
{
lean_object* v_fst_1947_; lean_object* v_fst_1948_; uint8_t v___x_1949_; 
v_fst_1947_ = lean_ctor_get(v_x1_1945_, 0);
v_fst_1948_ = lean_ctor_get(v_x2_1946_, 0);
v___x_1949_ = l_Lean_Name_quickLt(v_fst_1947_, v_fst_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_1950_, lean_object* v_x2_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_1950_, v_x2_1951_);
lean_dec_ref(v_x2_1951_);
lean_dec_ref(v_x1_1950_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_1955_, lean_object* v_lo_1956_, lean_object* v_hi_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_lt(v_lo_1956_, v_hi_1957_);
if (v___x_1958_ == 0)
{
lean_dec(v_lo_1956_);
return v_as_1955_;
}
else
{
lean_object* v___f_1959_; lean_object* v___x_1960_; lean_object* v_fst_1961_; lean_object* v_snd_1962_; uint8_t v___x_1963_; 
v___f_1959_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_1956_);
v___x_1960_ = l_Array_qpartition___redArg(v_as_1955_, v___f_1959_, v_lo_1956_, v_hi_1957_);
v_fst_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_fst_1961_);
v_snd_1962_ = lean_ctor_get(v___x_1960_, 1);
lean_inc(v_snd_1962_);
lean_dec_ref(v___x_1960_);
v___x_1963_ = lean_nat_dec_le(v_hi_1957_, v_fst_1961_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_snd_1962_, v_lo_1956_, v_fst_1961_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_add(v_fst_1961_, v___x_1965_);
lean_dec(v_fst_1961_);
v_as_1955_ = v___x_1964_;
v_lo_1956_ = v___x_1966_;
goto _start;
}
else
{
lean_dec(v_fst_1961_);
lean_dec(v_lo_1956_);
return v_snd_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_1968_, lean_object* v_lo_1969_, lean_object* v_hi_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_as_1968_, v_lo_1969_, v_hi_1970_);
lean_dec(v_hi_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_x_1974_, lean_object* v_s_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1978_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1977_, v_s_1975_);
v___x_1984_ = lean_array_get_size(v___x_1978_);
v___x_1985_ = lean_nat_dec_eq(v___x_1984_, v___x_1976_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___y_1989_; uint8_t v___x_1991_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_sub(v___x_1984_, v___x_1986_);
v___x_1991_ = lean_nat_dec_le(v___x_1976_, v___x_1987_);
if (v___x_1991_ == 0)
{
lean_inc(v___x_1987_);
v___y_1989_ = v___x_1987_;
goto v___jp_1988_;
}
else
{
v___y_1989_ = v___x_1976_;
goto v___jp_1988_;
}
v___jp_1988_:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_nat_dec_le(v___y_1989_, v___x_1987_);
if (v___x_1990_ == 0)
{
lean_dec(v___x_1987_);
lean_inc(v___y_1989_);
v___y_1980_ = v___y_1989_;
v___y_1981_ = v___y_1989_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v___y_1989_;
v___y_1981_ = v___x_1987_;
goto v___jp_1979_;
}
}
}
else
{
lean_object* v___x_1992_; 
lean_inc_ref_n(v___x_1978_, 2);
v___x_1992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1978_);
lean_ctor_set(v___x_1992_, 1, v___x_1978_);
lean_ctor_set(v___x_1992_, 2, v___x_1978_);
return v___x_1992_;
}
v___jp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1978_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_inc_ref_n(v___x_1982_, 2);
v___x_1983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_ctor_set(v___x_1983_, 2, v___x_1982_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_x_1993_, lean_object* v_s_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_x_1993_, v_s_1994_);
lean_dec(v_s_1994_);
lean_dec_ref(v_x_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v_es_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v___x_1998_, v_es_1996_);
v___x_2000_ = lean_array_get_size(v___x_1999_);
v___x_2001_ = lean_nat_dec_eq(v___x_2000_, v___x_1997_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___y_2005_; uint8_t v___x_2009_; 
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_nat_sub(v___x_2000_, v___x_2002_);
v___x_2009_ = lean_nat_dec_le(v___x_1997_, v___x_2003_);
if (v___x_2009_ == 0)
{
lean_inc(v___x_2003_);
v___y_2005_ = v___x_2003_;
goto v___jp_2004_;
}
else
{
v___y_2005_ = v___x_1997_;
goto v___jp_2004_;
}
v___jp_2004_:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_nat_dec_le(v___y_2005_, v___x_2003_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_dec(v___x_2003_);
lean_inc(v___y_2005_);
v___x_2007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1999_, v___y_2005_, v___y_2005_);
lean_dec(v___y_2005_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v___x_1999_, v___y_2005_, v___x_2003_);
lean_dec(v___x_2003_);
return v___x_2008_;
}
}
}
else
{
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_es_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v_es_2010_);
lean_dec(v_es_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(lean_object* v___x_2012_, lean_object* v_x_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2012_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v___x_2017_, lean_object* v_x_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(v___x_2017_, v_x_2018_, v___y_2019_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_x_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v___x_2048_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2____boxed(lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_();
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(lean_object* v_init_2051_, lean_object* v_t_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0_spec__0(v_init_2051_, v_t_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2054_, lean_object* v_t_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__0(v_init_2054_, v_t_2055_);
lean_dec(v_t_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(lean_object* v_n_2057_, lean_object* v_as_2058_, lean_object* v_lo_2059_, lean_object* v_hi_2060_, lean_object* v_w_2061_, lean_object* v_hlo_2062_, lean_object* v_hhi_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg(v_as_2058_, v_lo_2059_, v_hi_2060_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_2065_, lean_object* v_as_2066_, lean_object* v_lo_2067_, lean_object* v_hi_2068_, lean_object* v_w_2069_, lean_object* v_hlo_2070_, lean_object* v_hhi_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1(v_n_2065_, v_as_2066_, v_lo_2067_, v_hi_2068_, v_w_2069_, v_hlo_2070_, v_hhi_2071_);
lean_dec(v_hi_2068_);
lean_dec(v_n_2065_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1(lean_object* v_tag_2077_, lean_object* v___x_2078_, lean_object* v_toPure_2079_, lean_object* v___f_2080_, lean_object* v_env_2081_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2081_, v_tag_2077_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; lean_object* v_toEnvExtension_2087_; lean_object* v_asyncMode_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec_ref(v___f_2080_);
v___x_2086_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2087_ = lean_ctor_get(v___x_2086_, 0);
v_asyncMode_2088_ = lean_ctor_get(v_toEnvExtension_2087_, 2);
v___x_2089_ = lean_box(0);
v___x_2090_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2078_, v___x_2086_, v_env_2081_, v_asyncMode_2088_, v___x_2089_);
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2090_, v_tag_2077_);
lean_dec(v_tag_2077_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2091_);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_val_2093_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_val_2093_);
lean_dec_ref(v___x_2085_);
v___x_2094_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2095_ = 0;
v___x_2096_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2078_, v___x_2094_, v_env_2081_, v_val_2093_, v___x_2095_);
lean_dec(v_val_2093_);
lean_dec_ref(v_env_2081_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = lean_array_get_size(v___x_2096_);
v___x_2099_ = lean_nat_dec_lt(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v___x_2096_);
lean_dec_ref(v___f_2080_);
lean_dec(v_tag_2077_);
goto v___jp_2082_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_nat_sub(v___x_2098_, v___x_2100_);
v___x_2102_ = lean_nat_dec_le(v___x_2097_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2096_);
lean_dec_ref(v___f_2080_);
lean_dec(v_tag_2077_);
goto v___jp_2082_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_tag_2077_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__1));
v___x_2106_ = l_Array_binSearchAux___redArg(v___f_2080_, v___x_2105_, v___x_2096_, v___x_2104_, v___x_2097_, v___x_2101_);
lean_dec_ref(v___x_2096_);
if (lean_obj_tag(v___x_2106_) == 0)
{
goto v___jp_2082_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2116_; 
v_val_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2116_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_val_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2116_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_snd_2111_; lean_object* v___x_2113_; 
v_snd_2111_ = lean_ctor_get(v_val_2107_, 1);
lean_inc(v_snd_2111_);
lean_dec(v_val_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v_snd_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_snd_2111_);
v___x_2113_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2113_);
return v___x_2114_;
}
}
}
}
}
}
v___jp_2082_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2083_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___redArg(lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_tag_2119_){
_start:
{
lean_object* v_toApplicative_2120_; lean_object* v_toBind_2121_; lean_object* v_getEnv_2122_; lean_object* v_toPure_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; 
v_toApplicative_2120_ = lean_ctor_get(v_inst_2117_, 0);
lean_inc_ref(v_toApplicative_2120_);
v_toBind_2121_ = lean_ctor_get(v_inst_2117_, 1);
lean_inc(v_toBind_2121_);
lean_dec_ref(v_inst_2117_);
v_getEnv_2122_ = lean_ctor_get(v_inst_2118_, 0);
lean_inc(v_getEnv_2122_);
lean_dec_ref(v_inst_2118_);
v_toPure_2123_ = lean_ctor_get(v_toApplicative_2120_, 1);
lean_inc(v_toPure_2123_);
lean_dec_ref(v_toApplicative_2120_);
v___f_2124_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_2125_ = lean_box(1);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2126_, 0, v_tag_2119_);
lean_closure_set(v___f_2126_, 1, v___x_2125_);
lean_closure_set(v___f_2126_, 2, v_toPure_2123_);
lean_closure_set(v___f_2126_, 3, v___f_2124_);
v___x_2127_ = lean_apply_4(v_toBind_2121_, lean_box(0), lean_box(0), v_getEnv_2122_, v___f_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo(lean_object* v_m_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_tag_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Parser_Tactic_Doc_tagInfo___redArg(v_inst_2129_, v_inst_2130_, v_tag_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__0(lean_object* v_l_2133_, lean_object* v_k_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_array_push(v_l_2133_, v_k_2134_);
return v___x_2136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(lean_object* v_x1_2137_, lean_object* v_x2_2138_){
_start:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = 1;
v___x_2140_ = l_Lean_Name_toString(v_x1_2137_, v___x_2139_);
v___x_2141_ = l_Lean_Name_toString(v_x2_2138_, v___x_2139_);
v___x_2142_ = lean_string_dec_lt(v___x_2140_, v___x_2141_);
lean_dec_ref(v___x_2141_);
lean_dec_ref(v___x_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1___boxed(lean_object* v_x1_2143_, lean_object* v_x2_2144_){
_start:
{
uint8_t v_res_2145_; lean_object* v_r_2146_; 
v_res_2145_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__1(v_x1_2143_, v_x2_2144_);
v_r_2146_ = lean_box(v_res_2145_);
return v_r_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(lean_object* v_toPure_2147_, lean_object* v_a_2148_, lean_object* v_b_2149_, lean_object* v_c_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = l_Lean_NameSet_insert(v_c_2150_, v_a_2148_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
v___x_2153_ = lean_apply_2(v_toPure_2147_, lean_box(0), v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed(lean_object* v_toPure_2154_, lean_object* v_a_2155_, lean_object* v_b_2156_, lean_object* v_c_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3(v_toPure_2154_, v_a_2155_, v_b_2156_, v_c_2157_);
lean_dec_ref(v_b_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2(lean_object* v_toPure_2159_, lean_object* v_a_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_fst_2163_; lean_object* v_found_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_fst_2163_ = lean_ctor_get(v_a_2160_, 0);
lean_inc(v_fst_2163_);
lean_dec_ref(v_a_2160_);
v_found_2164_ = l_Lean_NameSet_insert(v___y_2162_, v_fst_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_found_2164_);
v___x_2166_ = lean_apply_2(v_toPure_2159_, lean_box(0), v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5(lean_object* v_inst_2167_, lean_object* v___f_2168_, lean_object* v_toBind_2169_, lean_object* v___f_2170_, lean_object* v_a_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_){
_start:
{
size_t v_sz_2174_; size_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_sz_2174_ = lean_array_size(v_a_2171_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2167_, v_a_2171_, v___f_2168_, v_sz_2174_, v___x_2175_, v___y_2173_);
v___x_2177_ = lean_apply_4(v_toBind_2169_, lean_box(0), lean_box(0), v___x_2176_, v___f_2170_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4(lean_object* v_toPure_2178_, lean_object* v___f_2179_, lean_object* v___f_2180_, lean_object* v_____s_2181_){
_start:
{
lean_object* v___y_2183_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2199_; 
if (lean_obj_tag(v_____s_2181_) == 0)
{
lean_object* v_size_2208_; 
v_size_2208_ = lean_ctor_get(v_____s_2181_, 0);
lean_inc(v_size_2208_);
v___y_2199_ = v_size_2208_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_unsigned_to_nat(0u);
v___y_2199_ = v___x_2209_;
goto v___jp_2198_;
}
v___jp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_array_to_list(v___y_2183_);
v___x_2185_ = lean_apply_2(v_toPure_2178_, lean_box(0), v___x_2184_);
return v___x_2185_;
}
v___jp_2186_:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2179_, v___y_2189_, v___y_2187_, v___y_2188_, v___y_2190_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
v___y_2183_ = v___x_2191_;
goto v___jp_2182_;
}
v___jp_2192_:
{
uint8_t v___x_2197_; 
v___x_2197_ = lean_nat_dec_le(v___y_2196_, v___y_2195_);
if (v___x_2197_ == 0)
{
lean_dec(v___y_2195_);
lean_inc(v___y_2196_);
v___y_2187_ = v___y_2193_;
v___y_2188_ = v___y_2196_;
v___y_2189_ = v___y_2194_;
v___y_2190_ = v___y_2196_;
goto v___jp_2186_;
}
else
{
v___y_2187_ = v___y_2193_;
v___y_2188_ = v___y_2196_;
v___y_2189_ = v___y_2194_;
v___y_2190_ = v___y_2195_;
goto v___jp_2186_;
}
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2200_ = lean_mk_empty_array_with_capacity(v___y_2199_);
lean_dec(v___y_2199_);
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2180_, v___x_2200_, v_____s_2181_);
v___x_2202_ = lean_array_get_size(v___x_2201_);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_nat_dec_eq(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_sub(v___x_2202_, v___x_2205_);
v___x_2207_ = lean_nat_dec_le(v___x_2203_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_inc(v___x_2206_);
v___y_2193_ = v___x_2201_;
v___y_2194_ = v___x_2202_;
v___y_2195_ = v___x_2206_;
v___y_2196_ = v___x_2206_;
goto v___jp_2192_;
}
else
{
v___y_2193_ = v___x_2201_;
v___y_2194_ = v___x_2202_;
v___y_2195_ = v___x_2206_;
v___y_2196_ = v___x_2203_;
goto v___jp_2192_;
}
}
else
{
lean_dec_ref(v___f_2179_);
v___y_2183_ = v___x_2201_;
goto v___jp_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(lean_object* v___x_2210_, lean_object* v_toEnvExtension_2211_, lean_object* v_env_2212_, lean_object* v_asyncMode_2213_, lean_object* v___x_2214_, lean_object* v_inst_2215_, lean_object* v___f_2216_, lean_object* v_toBind_2217_, lean_object* v___f_2218_, lean_object* v_____s_2219_){
_start:
{
lean_object* v___x_2220_; lean_object* v_importedEntries_2221_; size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2220_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2210_, v_toEnvExtension_2211_, v_env_2212_, v_asyncMode_2213_, v___x_2214_);
v_importedEntries_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_importedEntries_2221_);
lean_dec(v___x_2220_);
v_sz_2222_ = lean_array_size(v_importedEntries_2221_);
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2215_, v_importedEntries_2221_, v___f_2216_, v_sz_2222_, v___x_2223_, v_____s_2219_);
v___x_2225_ = lean_apply_4(v_toBind_2217_, lean_box(0), lean_box(0), v___x_2224_, v___f_2218_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed(lean_object* v___x_2226_, lean_object* v_toEnvExtension_2227_, lean_object* v_env_2228_, lean_object* v_asyncMode_2229_, lean_object* v___x_2230_, lean_object* v_inst_2231_, lean_object* v___f_2232_, lean_object* v_toBind_2233_, lean_object* v___f_2234_, lean_object* v_____s_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6(v___x_2226_, v_toEnvExtension_2227_, v_env_2228_, v_asyncMode_2229_, v___x_2230_, v_inst_2231_, v___f_2232_, v_toBind_2233_, v___f_2234_, v_____s_2235_);
lean_dec(v_asyncMode_2229_);
lean_dec_ref(v_toEnvExtension_2227_);
lean_dec_ref(v___x_2226_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7(lean_object* v___x_2237_, lean_object* v_inst_2238_, lean_object* v___f_2239_, lean_object* v_toBind_2240_, lean_object* v___f_2241_, lean_object* v___x_2242_, lean_object* v___f_2243_, lean_object* v___f_2244_, lean_object* v_env_2245_){
_start:
{
lean_object* v___x_2246_; lean_object* v_toEnvExtension_2247_; lean_object* v_asyncMode_2248_; lean_object* v_found_2249_; lean_object* v___x_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2246_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2247_ = lean_ctor_get(v___x_2246_, 0);
v_asyncMode_2248_ = lean_ctor_get(v_toEnvExtension_2247_, 2);
v_found_2249_ = l_Lean_NameSet_empty;
v___x_2250_ = lean_box(0);
lean_inc_n(v_toBind_2240_, 2);
lean_inc_ref(v_inst_2238_);
lean_inc(v_asyncMode_2248_);
lean_inc_ref(v_env_2245_);
lean_inc_ref(v_toEnvExtension_2247_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2251_, 0, v___x_2237_);
lean_closure_set(v___f_2251_, 1, v_toEnvExtension_2247_);
lean_closure_set(v___f_2251_, 2, v_env_2245_);
lean_closure_set(v___f_2251_, 3, v_asyncMode_2248_);
lean_closure_set(v___f_2251_, 4, v___x_2250_);
lean_closure_set(v___f_2251_, 5, v_inst_2238_);
lean_closure_set(v___f_2251_, 6, v___f_2239_);
lean_closure_set(v___f_2251_, 7, v_toBind_2240_);
lean_closure_set(v___f_2251_, 8, v___f_2241_);
v___x_2252_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2242_, v___x_2246_, v_env_2245_, v_asyncMode_2248_, v___x_2250_);
v___x_2253_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2238_, v___f_2243_, v_found_2249_, v___x_2252_);
v___x_2254_ = lean_apply_4(v_toBind_2240_, lean_box(0), lean_box(0), v___x_2253_, v___f_2244_);
v___x_2255_ = lean_apply_4(v_toBind_2240_, lean_box(0), lean_box(0), v___x_2254_, v___f_2251_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(1);
v___x_2259_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___redArg(lean_object* v_inst_2260_, lean_object* v_inst_2261_){
_start:
{
lean_object* v_toApplicative_2262_; lean_object* v_toBind_2263_; lean_object* v_getEnv_2264_; lean_object* v_toPure_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; 
v_toApplicative_2262_ = lean_ctor_get(v_inst_2260_, 0);
v_toBind_2263_ = lean_ctor_get(v_inst_2260_, 1);
lean_inc_n(v_toBind_2263_, 3);
v_getEnv_2264_ = lean_ctor_get(v_inst_2261_, 0);
lean_inc(v_getEnv_2264_);
lean_dec_ref(v_inst_2261_);
v_toPure_2265_ = lean_ctor_get(v_toApplicative_2262_, 1);
v___f_2266_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__0));
v___f_2267_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__1));
v___x_2268_ = lean_box(1);
v___x_2269_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2265_, 5);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2270_, 0, v_toPure_2265_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2271_, 0, v_toPure_2265_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2272_, 0, v_toPure_2265_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2273_, 0, v_toPure_2265_);
lean_inc_ref(v_inst_2260_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2274_, 0, v_inst_2260_);
lean_closure_set(v___f_2274_, 1, v___f_2272_);
lean_closure_set(v___f_2274_, 2, v_toBind_2263_);
lean_closure_set(v___f_2274_, 3, v___f_2273_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2275_, 0, v_toPure_2265_);
lean_closure_set(v___f_2275_, 1, v___f_2267_);
lean_closure_set(v___f_2275_, 2, v___f_2266_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__7), 9, 8);
lean_closure_set(v___f_2276_, 0, v___x_2269_);
lean_closure_set(v___f_2276_, 1, v_inst_2260_);
lean_closure_set(v___f_2276_, 2, v___f_2274_);
lean_closure_set(v___f_2276_, 3, v_toBind_2263_);
lean_closure_set(v___f_2276_, 4, v___f_2275_);
lean_closure_set(v___f_2276_, 5, v___x_2268_);
lean_closure_set(v___f_2276_, 6, v___f_2271_);
lean_closure_set(v___f_2276_, 7, v___f_2270_);
v___x_2277_ = lean_apply_4(v_toBind_2263_, lean_box(0), lean_box(0), v_getEnv_2264_, v___f_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags(lean_object* v_m_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Parser_Tactic_Doc_allTags___redArg(v_inst_2279_, v_inst_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__0(lean_object* v_arr_2282_, lean_object* v_k_2283_, lean_object* v_v_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_k_2283_);
lean_ctor_set(v___x_2285_, 1, v_v_2284_);
v___x_2286_ = lean_array_push(v_arr_2282_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(lean_object* v_x1_2287_, lean_object* v_x2_2288_){
_start:
{
lean_object* v_fst_2289_; lean_object* v_fst_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_fst_2289_ = lean_ctor_get(v_x1_2287_, 0);
lean_inc(v_fst_2289_);
lean_dec_ref(v_x1_2287_);
v_fst_2290_ = lean_ctor_get(v_x2_2288_, 0);
lean_inc(v_fst_2290_);
lean_dec_ref(v_x2_2288_);
v___x_2291_ = 1;
v___x_2292_ = l_Lean_Name_toString(v_fst_2289_, v___x_2291_);
v___x_2293_ = l_Lean_Name_toString(v_fst_2290_, v___x_2291_);
v___x_2294_ = lean_string_dec_lt(v___x_2292_, v___x_2293_);
lean_dec_ref(v___x_2293_);
lean_dec_ref(v___x_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1___boxed(lean_object* v_x1_2295_, lean_object* v_x2_2296_){
_start:
{
uint8_t v_res_2297_; lean_object* v_r_2298_; 
v_res_2297_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__1(v_x1_2295_, v_x2_2296_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3(lean_object* v_toPure_2299_, lean_object* v_a_2300_, lean_object* v_b_2301_, lean_object* v_c_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_a_2300_, v_b_2301_, v_c_2302_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
v___x_2305_ = lean_apply_2(v_toPure_2299_, lean_box(0), v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2(lean_object* v_toPure_2306_, lean_object* v_a_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v_found_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_fst_2310_ = lean_ctor_get(v_a_2307_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v_a_2307_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v_a_2307_);
v_found_2312_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2310_, v_snd_2311_, v___y_2309_);
v___x_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_found_2312_);
v___x_2314_ = lean_apply_2(v_toPure_2306_, lean_box(0), v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6(lean_object* v_toPure_2315_, lean_object* v___f_2316_, lean_object* v___f_2317_, lean_object* v_____s_2318_){
_start:
{
lean_object* v___y_2320_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_arr_2325_; lean_object* v___x_2326_; lean_object* v___y_2328_; lean_object* v___y_2329_; uint8_t v___x_2331_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2_));
v_arr_2325_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2316_, v___x_2324_, v_____s_2318_);
v___x_2326_ = lean_array_get_size(v_arr_2325_);
v___x_2331_ = lean_nat_dec_eq(v___x_2326_, v___x_2323_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___y_2335_; uint8_t v___x_2337_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_sub(v___x_2326_, v___x_2332_);
v___x_2337_ = lean_nat_dec_le(v___x_2323_, v___x_2333_);
if (v___x_2337_ == 0)
{
lean_inc(v___x_2333_);
v___y_2335_ = v___x_2333_;
goto v___jp_2334_;
}
else
{
v___y_2335_ = v___x_2323_;
goto v___jp_2334_;
}
v___jp_2334_:
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_nat_dec_le(v___y_2335_, v___x_2333_);
if (v___x_2336_ == 0)
{
lean_dec(v___x_2333_);
lean_inc(v___y_2335_);
v___y_2328_ = v___y_2335_;
v___y_2329_ = v___y_2335_;
goto v___jp_2327_;
}
else
{
v___y_2328_ = v___y_2335_;
v___y_2329_ = v___x_2333_;
goto v___jp_2327_;
}
}
}
else
{
lean_dec_ref(v___f_2317_);
v___y_2320_ = v_arr_2325_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_array_to_list(v___y_2320_);
v___x_2322_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2321_);
return v___x_2322_;
}
v___jp_2327_:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2317_, v___x_2326_, v_arr_2325_, v___y_2328_, v___y_2329_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2329_);
v___y_2320_ = v___x_2330_;
goto v___jp_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5(lean_object* v___x_2338_, lean_object* v_inst_2339_, lean_object* v___f_2340_, lean_object* v_toBind_2341_, lean_object* v___f_2342_, lean_object* v___x_2343_, lean_object* v___f_2344_, lean_object* v___f_2345_, lean_object* v_env_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v_toEnvExtension_2348_; lean_object* v_asyncMode_2349_; lean_object* v_found_2350_; lean_object* v___x_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2347_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2348_ = lean_ctor_get(v___x_2347_, 0);
v_asyncMode_2349_ = lean_ctor_get(v_toEnvExtension_2348_, 2);
v_found_2350_ = lean_box(1);
v___x_2351_ = lean_box(0);
lean_inc_n(v_toBind_2341_, 2);
lean_inc_ref(v_inst_2339_);
lean_inc(v_asyncMode_2349_);
lean_inc_ref(v_env_2346_);
lean_inc_ref(v_toEnvExtension_2348_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_2352_, 0, v___x_2338_);
lean_closure_set(v___f_2352_, 1, v_toEnvExtension_2348_);
lean_closure_set(v___f_2352_, 2, v_env_2346_);
lean_closure_set(v___f_2352_, 3, v_asyncMode_2349_);
lean_closure_set(v___f_2352_, 4, v___x_2351_);
lean_closure_set(v___f_2352_, 5, v_inst_2339_);
lean_closure_set(v___f_2352_, 6, v___f_2340_);
lean_closure_set(v___f_2352_, 7, v_toBind_2341_);
lean_closure_set(v___f_2352_, 8, v___f_2342_);
v___x_2353_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2343_, v___x_2347_, v_env_2346_, v_asyncMode_2349_, v___x_2351_);
v___x_2354_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2339_, v___f_2344_, v_found_2350_, v___x_2353_);
v___x_2355_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v___x_2354_, v___f_2345_);
v___x_2356_ = lean_apply_4(v_toBind_2341_, lean_box(0), lean_box(0), v___x_2355_, v___f_2352_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(lean_object* v_inst_2359_, lean_object* v_inst_2360_){
_start:
{
lean_object* v_toApplicative_2361_; lean_object* v_toBind_2362_; lean_object* v_getEnv_2363_; lean_object* v_toPure_2364_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; 
v_toApplicative_2361_ = lean_ctor_get(v_inst_2359_, 0);
v_toBind_2362_ = lean_ctor_get(v_inst_2359_, 1);
lean_inc_n(v_toBind_2362_, 3);
v_getEnv_2363_ = lean_ctor_get(v_inst_2360_, 0);
lean_inc(v_getEnv_2363_);
lean_dec_ref(v_inst_2360_);
v_toPure_2364_ = lean_ctor_get(v_toApplicative_2361_, 1);
v___f_2365_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__0));
v___f_2366_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___closed__1));
v___x_2367_ = lean_box(1);
v___x_2368_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
lean_inc_n(v_toPure_2364_, 5);
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2369_, 0, v_toPure_2364_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__3), 4, 1);
lean_closure_set(v___f_2370_, 0, v_toPure_2364_);
v___f_2371_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__2), 4, 1);
lean_closure_set(v___f_2371_, 0, v_toPure_2364_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_aliases___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2372_, 0, v_toPure_2364_);
lean_inc_ref(v_inst_2359_);
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTags___redArg___lam__5), 7, 4);
lean_closure_set(v___f_2373_, 0, v_inst_2359_);
lean_closure_set(v___f_2373_, 1, v___f_2371_);
lean_closure_set(v___f_2373_, 2, v_toBind_2362_);
lean_closure_set(v___f_2373_, 3, v___f_2372_);
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__6), 4, 3);
lean_closure_set(v___f_2374_, 0, v_toPure_2364_);
lean_closure_set(v___f_2374_, 1, v___f_2365_);
lean_closure_set(v___f_2374_, 2, v___f_2366_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2375_, 0, v___x_2368_);
lean_closure_set(v___f_2375_, 1, v_inst_2359_);
lean_closure_set(v___f_2375_, 2, v___f_2373_);
lean_closure_set(v___f_2375_, 3, v_toBind_2362_);
lean_closure_set(v___f_2375_, 4, v___f_2374_);
lean_closure_set(v___f_2375_, 5, v___x_2367_);
lean_closure_set(v___f_2375_, 6, v___f_2370_);
lean_closure_set(v___f_2375_, 7, v___f_2369_);
v___x_2376_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v_getEnv_2363_, v___f_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo(lean_object* v_m_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___redArg(v_inst_2378_, v_inst_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(lean_object* v_a_2381_, lean_object* v_init_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
lean_object* v_k_2384_; lean_object* v_l_2385_; lean_object* v_r_2386_; lean_object* v___x_2387_; lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_k_2384_ = lean_ctor_get(v_x_2383_, 1);
v_l_2385_ = lean_ctor_get(v_x_2383_, 3);
v_r_2386_ = lean_ctor_get(v_x_2383_, 4);
lean_inc_n(v_a_2381_, 2);
v___x_2387_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2381_, v_init_2382_, v_l_2385_);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref(v___x_2387_);
lean_inc(v_k_2384_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_a_2381_);
lean_ctor_set(v___x_2389_, 1, v_k_2384_);
v___x_2390_ = lean_array_push(v_a_2388_, v___x_2389_);
v_init_2382_ = v___x_2390_;
v_x_2383_ = v_r_2386_;
goto _start;
}
else
{
lean_object* v___x_2392_; 
lean_dec(v_a_2381_);
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_init_2382_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1___boxed(lean_object* v_a_2393_, lean_object* v_init_2394_, lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_a_2393_, v_init_2394_, v_x_2395_);
lean_dec(v_x_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(lean_object* v_init_2397_, lean_object* v_x_2398_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 0)
{
lean_object* v_k_2399_; lean_object* v_v_2400_; lean_object* v_l_2401_; lean_object* v_r_2402_; lean_object* v___x_2403_; lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v_a_2406_; 
v_k_2399_ = lean_ctor_get(v_x_2398_, 1);
lean_inc(v_k_2399_);
v_v_2400_ = lean_ctor_get(v_x_2398_, 2);
lean_inc(v_v_2400_);
v_l_2401_ = lean_ctor_get(v_x_2398_, 3);
lean_inc(v_l_2401_);
v_r_2402_ = lean_ctor_get(v_x_2398_, 4);
lean_inc(v_r_2402_);
lean_dec_ref(v_x_2398_);
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_init_2397_, v_l_2401_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__1(v_k_2399_, v_a_2404_, v_v_2400_);
lean_dec(v_v_2400_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___x_2405_);
v_init_2397_ = v_a_2406_;
v_x_2398_ = v_r_2402_;
goto _start;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_init_2397_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2409_){
_start:
{
lean_object* v_exported_2410_; lean_object* v___x_2411_; lean_object* v_a_2412_; 
v_exported_2410_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2411_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2410_, v_tags_2409_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref(v___x_2411_);
return v_a_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_x_2413_, lean_object* v_s_2414_){
_start:
{
lean_object* v_exported_2415_; lean_object* v___x_2416_; lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_exported_2415_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_44007290____hygCtx___hyg_2_));
v___x_2416_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__2(v_exported_2415_, v_s_2414_);
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc_n(v_a_2417_, 3);
lean_dec_ref(v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2418_, 0, v_a_2417_);
lean_ctor_set(v___x_2418_, 1, v_a_2417_);
lean_ctor_set(v___x_2418_, 2, v_a_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_x_2419_, lean_object* v_s_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(v_x_2419_, v_s_2420_);
lean_dec_ref(v_x_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(lean_object* v_t_2422_, lean_object* v_k_2423_, lean_object* v_fallback_2424_){
_start:
{
if (lean_obj_tag(v_t_2422_) == 0)
{
lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v_l_2427_; lean_object* v_r_2428_; uint8_t v___x_2429_; 
v_k_2425_ = lean_ctor_get(v_t_2422_, 1);
v_v_2426_ = lean_ctor_get(v_t_2422_, 2);
v_l_2427_ = lean_ctor_get(v_t_2422_, 3);
v_r_2428_ = lean_ctor_get(v_t_2422_, 4);
v___x_2429_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2423_, v_k_2425_);
switch(v___x_2429_)
{
case 0:
{
v_t_2422_ = v_l_2427_;
goto _start;
}
case 1:
{
lean_inc(v_v_2426_);
return v_v_2426_;
}
default: 
{
v_t_2422_ = v_r_2428_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2424_);
return v_fallback_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_t_2432_, lean_object* v_k_2433_, lean_object* v_fallback_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2432_, v_k_2433_, v_fallback_2434_);
lean_dec(v_fallback_2434_);
lean_dec(v_k_2433_);
lean_dec(v_t_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(lean_object* v_tags_2436_, lean_object* v_x_2437_){
_start:
{
lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_fst_2438_ = lean_ctor_get(v_x_2437_, 0);
lean_inc(v_fst_2438_);
v_snd_2439_ = lean_ctor_get(v_x_2437_, 1);
lean_inc(v_snd_2439_);
lean_dec_ref(v_x_2437_);
v___x_2440_ = l_Lean_NameSet_empty;
v___x_2441_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_tags_2436_, v_fst_2438_, v___x_2440_);
v___x_2442_ = l_Lean_NameSet_insert(v___x_2441_, v_snd_2439_);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2438_, v___x_2442_, v_tags_2436_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_));
v___x_2468_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2____boxed(lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2_();
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b4_2471_, lean_object* v_t_2472_, lean_object* v_k_2473_, lean_object* v_fallback_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_t_2472_, v_k_2473_, v_fallback_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b4_2476_, lean_object* v_t_2477_, lean_object* v_k_2478_, lean_object* v_fallback_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0(v_00_u03b4_2476_, v_t_2477_, v_k_2478_, v_fallback_2479_);
lean_dec(v_fallback_2479_);
lean_dec(v_k_2478_);
lean_dec(v_t_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v_name_2481_, lean_object* v_decl_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2486_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__1_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2487_ = l_Lean_MessageData_ofName(v_name_2481_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__3_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_2490_, v___y_2483_, v___y_2484_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_name_2492_, lean_object* v_decl_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v_name_2492_, v_decl_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v_decl_2493_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
if (lean_obj_tag(v_a_2498_) == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = l_List_reverse___redArg(v_a_2499_);
return v___x_2500_;
}
else
{
lean_object* v_head_2501_; lean_object* v_tail_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2514_; 
v_head_2501_ = lean_ctor_get(v_a_2498_, 0);
v_tail_2502_ = lean_ctor_get(v_a_2498_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2504_ = v_a_2498_;
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_tail_2502_);
lean_inc(v_head_2501_);
lean_dec(v_a_2498_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2507_ = l_Lean_MessageData_ofName(v_head_2501_);
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2506_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v_a_2499_);
lean_ctor_set(v___x_2504_, 0, v___x_2509_);
v___x_2511_ = v___x_2504_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_a_2499_);
v___x_2511_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v_a_2498_ = v_tail_2502_;
v_a_2499_ = v___x_2511_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_2515_, lean_object* v_k_2516_, lean_object* v_x_2517_, lean_object* v_x_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_m_2521_; lean_object* v_a_2522_; uint8_t v___x_2523_; 
v___x_2519_ = lean_nat_add(v_x_2517_, v_x_2518_);
v___x_2520_ = lean_unsigned_to_nat(1u);
v_m_2521_ = lean_nat_shiftr(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
v_a_2522_ = lean_array_fget_borrowed(v_as_2515_, v_m_2521_);
v___x_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2522_, v_k_2516_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
lean_dec(v_x_2518_);
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3047250029____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_2516_, v_a_2522_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
lean_dec(v_m_2521_);
lean_dec(v_x_2517_);
lean_inc(v_a_2522_);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_a_2522_);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = lean_unsigned_to_nat(0u);
v___x_2527_ = lean_nat_dec_eq(v_m_2521_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = lean_nat_sub(v_m_2521_, v___x_2520_);
lean_dec(v_m_2521_);
v___x_2529_ = lean_nat_dec_lt(v___x_2528_, v_x_2517_);
if (v___x_2529_ == 0)
{
v_x_2518_ = v___x_2528_;
goto _start;
}
else
{
lean_object* v___x_2531_; 
lean_dec(v___x_2528_);
lean_dec(v_x_2517_);
v___x_2531_ = lean_box(0);
return v___x_2531_;
}
}
else
{
lean_object* v___x_2532_; 
lean_dec(v_m_2521_);
lean_dec(v_x_2517_);
v___x_2532_ = lean_box(0);
return v___x_2532_;
}
}
}
else
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
lean_dec(v_x_2517_);
v___x_2533_ = lean_nat_add(v_m_2521_, v___x_2520_);
lean_dec(v_m_2521_);
v___x_2534_ = lean_nat_dec_le(v___x_2533_, v_x_2518_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec(v___x_2533_);
lean_dec(v_x_2518_);
v___x_2535_ = lean_box(0);
return v___x_2535_;
}
else
{
v_x_2517_ = v___x_2533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_2537_, lean_object* v_k_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_2537_, v_k_2538_, v_x_2539_, v_x_2540_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_as_2537_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tag_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v_env_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2545_ = lean_st_ref_get(v___y_2543_);
v_env_2549_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_ref(v_env_2549_);
lean_dec(v___x_2545_);
v___x_2550_ = lean_box(1);
v___x_2551_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2549_, v_tag_2542_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2552_; lean_object* v_toEnvExtension_2553_; lean_object* v_asyncMode_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2552_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2553_ = lean_ctor_get(v___x_2552_, 0);
v_asyncMode_2554_ = lean_ctor_get(v_toEnvExtension_2553_, 2);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2550_, v___x_2552_, v_env_2549_, v_asyncMode_2554_, v___x_2555_);
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2556_, v_tag_2542_);
lean_dec(v_tag_2542_);
lean_dec(v___x_2556_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
else
{
lean_object* v_val_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2587_; 
v_val_2559_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2561_ = v___x_2551_;
v_isShared_2562_ = v_isSharedCheck_2587_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_val_2559_);
lean_dec(v___x_2551_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2587_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2563_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v___x_2564_ = 0;
v___x_2565_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2550_, v___x_2563_, v_env_2549_, v_val_2559_, v___x_2564_);
lean_dec(v_val_2559_);
lean_dec_ref(v_env_2549_);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_array_get_size(v___x_2565_);
v___x_2568_ = lean_nat_dec_lt(v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec_ref(v___x_2565_);
lean_del_object(v___x_2561_);
lean_dec(v_tag_2542_);
goto v___jp_2546_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_sub(v___x_2567_, v___x_2569_);
v___x_2571_ = lean_nat_dec_le(v___x_2566_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec(v___x_2570_);
lean_dec_ref(v___x_2565_);
lean_del_object(v___x_2561_);
lean_dec(v_tag_2542_);
goto v___jp_2546_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_tagInfo___redArg___lam__1___closed__0));
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_tag_2542_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_2565_, v___x_2573_, v___x_2566_, v___x_2570_);
lean_dec_ref(v___x_2573_);
lean_dec_ref(v___x_2565_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_del_object(v___x_2561_);
goto v___jp_2546_;
}
else
{
lean_object* v_val_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
v_val_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_val_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_snd_2579_; lean_object* v___x_2581_; 
v_snd_2579_ = lean_ctor_get(v_val_2575_, 1);
lean_inc(v_snd_2579_);
lean_dec(v_val_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v_snd_2579_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_snd_2579_);
v___x_2581_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2581_);
v___x_2583_ = v___x_2561_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tag_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_2588_, v___y_2589_);
lean_dec(v___y_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_as_2592_, size_t v_sz_2593_, size_t v_i_2594_, lean_object* v_b_2595_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_usize_dec_lt(v_i_2594_, v_sz_2593_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_b_2595_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v_fst_2600_; lean_object* v_found_2601_; size_t v___x_2602_; size_t v___x_2603_; 
v_a_2599_ = lean_array_uget_borrowed(v_as_2592_, v_i_2594_);
v_fst_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_fst_2600_);
v_found_2601_ = l_Lean_NameSet_insert(v_b_2595_, v_fst_2600_);
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2594_, v___x_2602_);
v_i_2594_ = v___x_2603_;
v_b_2595_ = v_found_2601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_as_2605_, lean_object* v_sz_2606_, lean_object* v_i_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_){
_start:
{
size_t v_sz_boxed_2610_; size_t v_i_boxed_2611_; lean_object* v_res_2612_; 
v_sz_boxed_2610_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2611_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_2605_, v_sz_boxed_2610_, v_i_boxed_2611_, v_b_2608_);
lean_dec_ref(v_as_2605_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_as_2613_, size_t v_sz_2614_, size_t v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_usize_dec_lt(v_i_2615_, v_sz_2614_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_b_2616_);
return v___x_2621_;
}
else
{
lean_object* v_a_2622_; size_t v_sz_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v_a_2622_ = lean_array_uget_borrowed(v_as_2613_, v_i_2615_);
v_sz_2623_ = lean_array_size(v_a_2622_);
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_2622_, v_sz_2623_, v___x_2624_, v_b_2616_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; size_t v___x_2627_; size_t v___x_2628_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref(v___x_2625_);
v___x_2627_ = ((size_t)1ULL);
v___x_2628_ = lean_usize_add(v_i_2615_, v___x_2627_);
v_i_2615_ = v___x_2628_;
v_b_2616_ = v_a_2626_;
goto _start;
}
else
{
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_as_2630_, lean_object* v_sz_2631_, lean_object* v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2631_);
lean_dec(v_sz_2631_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2632_);
lean_dec(v_i_2632_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_as_2630_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v_as_2630_);
return v_res_2639_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(uint8_t v___x_2640_, lean_object* v_x1_2641_, lean_object* v_x2_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = l_Lean_Name_toString(v_x1_2641_, v___x_2640_);
v___x_2644_ = l_Lean_Name_toString(v_x2_2642_, v___x_2640_);
v___x_2645_ = lean_string_dec_lt(v___x_2643_, v___x_2644_);
lean_dec_ref(v___x_2644_);
lean_dec_ref(v___x_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed(lean_object* v___x_2646_, lean_object* v_x1_2647_, lean_object* v_x2_2648_){
_start:
{
uint8_t v___x_7502__boxed_2649_; uint8_t v_res_2650_; lean_object* v_r_2651_; 
v___x_7502__boxed_2649_ = lean_unbox(v___x_2646_);
v_res_2650_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0(v___x_7502__boxed_2649_, v_x1_2647_, v_x2_2648_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_as_2652_, lean_object* v_lo_2653_, lean_object* v_hi_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_nat_dec_lt(v_lo_2653_, v_hi_2654_);
if (v___x_2655_ == 0)
{
lean_dec(v_lo_2653_);
return v_as_2652_;
}
else
{
lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; uint8_t v___x_2661_; 
v___x_2656_ = lean_box(v___x_2655_);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2657_, 0, v___x_2656_);
lean_inc(v_lo_2653_);
v___x_2658_ = l_Array_qpartition___redArg(v_as_2652_, v___f_2657_, v_lo_2653_, v_hi_2654_);
v_fst_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v___x_2658_, 1);
lean_inc(v_snd_2660_);
lean_dec_ref(v___x_2658_);
v___x_2661_ = lean_nat_dec_le(v_hi_2654_, v_fst_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_snd_2660_, v_lo_2653_, v_fst_2659_);
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_fst_2659_, v___x_2663_);
lean_dec(v_fst_2659_);
v_as_2652_ = v___x_2662_;
v_lo_2653_ = v___x_2664_;
goto _start;
}
else
{
lean_dec(v_fst_2659_);
lean_dec(v_lo_2653_);
return v_snd_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_as_2666_, lean_object* v_lo_2667_, lean_object* v_hi_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_as_2666_, v_lo_2667_, v_hi_2668_);
lean_dec(v_hi_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* v_init_2670_, lean_object* v_x_2671_){
_start:
{
if (lean_obj_tag(v_x_2671_) == 0)
{
lean_object* v_k_2673_; lean_object* v_l_2674_; lean_object* v_r_2675_; lean_object* v___x_2676_; lean_object* v_a_2677_; lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_k_2673_ = lean_ctor_get(v_x_2671_, 1);
lean_inc(v_k_2673_);
v_l_2674_ = lean_ctor_get(v_x_2671_, 3);
lean_inc(v_l_2674_);
v_r_2675_ = lean_ctor_get(v_x_2671_, 4);
lean_inc(v_r_2675_);
lean_dec_ref(v_x_2671_);
v___x_2676_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2670_, v_l_2674_);
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v_a_2678_ = lean_ctor_get(v_a_2677_, 0);
lean_inc(v_a_2678_);
lean_dec(v_a_2677_);
v___x_2679_ = l_Lean_NameSet_insert(v_a_2678_, v_k_2673_);
v_init_2670_ = v___x_2679_;
v_x_2671_ = v_r_2675_;
goto _start;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_init_2670_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* v_init_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_2683_, v_x_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(lean_object* v_init_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
lean_object* v_k_2689_; lean_object* v_l_2690_; lean_object* v_r_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_k_2689_ = lean_ctor_get(v_x_2688_, 1);
lean_inc(v_k_2689_);
v_l_2690_ = lean_ctor_get(v_x_2688_, 3);
lean_inc(v_l_2690_);
v_r_2691_ = lean_ctor_get(v_x_2688_, 4);
lean_inc(v_r_2691_);
lean_dec_ref(v_x_2688_);
v___x_2692_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_2687_, v_l_2690_);
v___x_2693_ = lean_array_push(v___x_2692_, v_k_2689_);
v_init_2687_ = v___x_2693_;
v_x_2688_ = v_r_2691_;
goto _start;
}
else
{
return v_init_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___y_2699_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___x_2725_; lean_object* v_env_2726_; lean_object* v___x_2727_; lean_object* v_toEnvExtension_2728_; lean_object* v_asyncMode_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_found_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v_a_2738_; lean_object* v_a_2755_; 
v___x_2725_ = lean_st_ref_get(v___y_2696_);
v_env_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_ref_n(v_env_2726_, 2);
lean_dec(v___x_2725_);
v___x_2727_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2728_ = lean_ctor_get(v___x_2727_, 0);
v_asyncMode_2729_ = lean_ctor_get(v_toEnvExtension_2728_, 2);
v___x_2730_ = lean_box(1);
v___x_2731_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2, &l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2_once, _init_l_Lean_Parser_Tactic_Doc_allTags___redArg___closed__2);
v_found_2732_ = l_Lean_NameSet_empty;
v___x_2733_ = lean_box(0);
v___x_2734_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2730_, v___x_2727_, v_env_2726_, v_asyncMode_2729_, v___x_2733_);
v___x_2735_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_found_2732_, v___x_2734_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref(v___x_2735_);
v_a_2755_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_a_2755_);
lean_dec(v_a_2736_);
v_a_2738_ = v_a_2755_;
goto v___jp_2737_;
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_array_to_list(v___y_2699_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
v___jp_2702_:
{
lean_object* v___x_2707_; 
lean_dec(v___y_2703_);
v___x_2707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v___y_2705_, v___y_2704_, v___y_2706_);
lean_dec(v___y_2706_);
v___y_2699_ = v___x_2707_;
goto v___jp_2698_;
}
v___jp_2708_:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_nat_dec_le(v___y_2712_, v___y_2709_);
if (v___x_2713_ == 0)
{
lean_dec(v___y_2709_);
lean_inc(v___y_2712_);
v___y_2703_ = v___y_2710_;
v___y_2704_ = v___y_2712_;
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2712_;
goto v___jp_2702_;
}
else
{
v___y_2703_ = v___y_2710_;
v___y_2704_ = v___y_2712_;
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2709_;
goto v___jp_2702_;
}
}
v___jp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2717_ = lean_mk_empty_array_with_capacity(v___y_2716_);
lean_dec(v___y_2716_);
v___x_2718_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v___x_2717_, v___y_2715_);
v___x_2719_ = lean_array_get_size(v___x_2718_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_nat_dec_eq(v___x_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_nat_sub(v___x_2719_, v___x_2722_);
v___x_2724_ = lean_nat_dec_le(v___x_2720_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_inc(v___x_2723_);
v___y_2709_ = v___x_2723_;
v___y_2710_ = v___x_2719_;
v___y_2711_ = v___x_2718_;
v___y_2712_ = v___x_2723_;
goto v___jp_2708_;
}
else
{
v___y_2709_ = v___x_2723_;
v___y_2710_ = v___x_2719_;
v___y_2711_ = v___x_2718_;
v___y_2712_ = v___x_2720_;
goto v___jp_2708_;
}
}
else
{
v___y_2699_ = v___x_2718_;
goto v___jp_2698_;
}
}
v___jp_2737_:
{
lean_object* v___x_2739_; lean_object* v_importedEntries_2740_; size_t v_sz_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v___x_2739_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2731_, v_toEnvExtension_2728_, v_env_2726_, v_asyncMode_2729_, v___x_2733_);
v_importedEntries_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc_ref(v_importedEntries_2740_);
lean_dec(v___x_2739_);
v_sz_2741_ = lean_array_size(v_importedEntries_2740_);
v___x_2742_ = ((size_t)0ULL);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__3(v_importedEntries_2740_, v_sz_2741_, v___x_2742_, v_a_2738_, v___y_2695_, v___y_2696_);
lean_dec_ref(v_importedEntries_2740_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
if (lean_obj_tag(v_a_2744_) == 0)
{
lean_object* v_size_2745_; 
v_size_2745_ = lean_ctor_get(v_a_2744_, 0);
lean_inc(v_size_2745_);
v___y_2715_ = v_a_2744_;
v___y_2716_ = v_size_2745_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_unsigned_to_nat(0u);
v___y_2715_ = v_a_2744_;
v___y_2716_ = v___x_2746_;
goto v___jp_2714_;
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_a_2747_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2743_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2743_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1___boxed(lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2759_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__0));
v___x_2762_ = l_Lean_stringToMessageData(v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__2));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__4));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__6));
v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__10));
v___x_2778_ = l_Lean_MessageData_ofFormat(v___x_2777_);
return v___x_2778_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__13));
v___x_2783_ = l_Lean_MessageData_ofFormat(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__15));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(lean_object* v_decl_2787_, lean_object* v_as_2788_, size_t v_sz_2789_, size_t v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_a_2796_; uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_lt(v_i_2790_, v_sz_2789_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec(v_decl_2787_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_b_2791_);
return v___x_2801_;
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2802_ = lean_array_uget_borrowed(v_as_2788_, v_i_2790_);
v___x_2803_ = l_Lean_TSyntax_getId(v_a_2802_);
lean_inc(v___x_2803_);
v___x_2804_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v___x_2803_, v___y_2793_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
v___x_2806_ = lean_box(0);
if (lean_obj_tag(v_a_2805_) == 1)
{
lean_object* v___x_2807_; lean_object* v_env_2808_; lean_object* v_nextMacroScope_2809_; lean_object* v_ngen_2810_; lean_object* v_auxDeclNGen_2811_; lean_object* v_traceState_2812_; lean_object* v_messages_2813_; lean_object* v_infoState_2814_; lean_object* v_snapshotTasks_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v_a_2805_);
v___x_2807_ = lean_st_ref_take(v___y_2793_);
v_env_2808_ = lean_ctor_get(v___x_2807_, 0);
v_nextMacroScope_2809_ = lean_ctor_get(v___x_2807_, 1);
v_ngen_2810_ = lean_ctor_get(v___x_2807_, 2);
v_auxDeclNGen_2811_ = lean_ctor_get(v___x_2807_, 3);
v_traceState_2812_ = lean_ctor_get(v___x_2807_, 4);
v_messages_2813_ = lean_ctor_get(v___x_2807_, 6);
v_infoState_2814_ = lean_ctor_get(v___x_2807_, 7);
v_snapshotTasks_2815_ = lean_ctor_get(v___x_2807_, 8);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2807_, 5);
lean_dec(v_unused_2831_);
v___x_2817_ = v___x_2807_;
v_isShared_2818_ = v_isSharedCheck_2830_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snapshotTasks_2815_);
lean_inc(v_infoState_2814_);
lean_inc(v_messages_2813_);
lean_inc(v_traceState_2812_);
lean_inc(v_auxDeclNGen_2811_);
lean_inc(v_ngen_2810_);
lean_inc(v_nextMacroScope_2809_);
lean_inc(v_env_2808_);
lean_dec(v___x_2807_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2830_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_toEnvExtension_2820_; lean_object* v_asyncMode_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2819_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2820_ = lean_ctor_get(v___x_2819_, 0);
v_asyncMode_2821_ = lean_ctor_get(v_toEnvExtension_2820_, 2);
v___x_2822_ = lean_box(0);
lean_inc(v_decl_2787_);
v___x_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_decl_2787_);
lean_ctor_set(v___x_2823_, 1, v___x_2803_);
v___x_2824_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2819_, v_env_2808_, v___x_2823_, v_asyncMode_2821_, v___x_2822_);
v___x_2825_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 5, v___x_2825_);
lean_ctor_set(v___x_2817_, 0, v___x_2824_);
v___x_2827_ = v___x_2817_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_nextMacroScope_2809_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_ngen_2810_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_auxDeclNGen_2811_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_traceState_2812_);
lean_ctor_set(v_reuseFailAlloc_2829_, 5, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2829_, 6, v_messages_2813_);
lean_ctor_set(v_reuseFailAlloc_2829_, 7, v_infoState_2814_);
lean_ctor_set(v_reuseFailAlloc_2829_, 8, v_snapshotTasks_2815_);
v___x_2827_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_st_ref_set(v___y_2793_, v___x_2827_);
v_a_2796_ = v___x_2806_;
goto v___jp_2795_;
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_a_2805_);
v___x_2832_ = l_Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1(v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___y_2835_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2832_);
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = l_List_lengthTR___redArg(v_a_2833_);
v___x_2849_ = lean_nat_dec_eq(v___x_2848_, v___x_2847_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = lean_unsigned_to_nat(1u);
v___x_2851_ = lean_nat_dec_eq(v___x_2848_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = lean_unsigned_to_nat(10u);
v___x_2853_ = lean_nat_dec_lt(v___x_2848_, v___x_2852_);
lean_dec(v___x_2848_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__8));
lean_inc(v_a_2833_);
v___x_2856_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_a_2833_, v_a_2833_, v___x_2852_, v___x_2855_);
lean_dec(v_a_2833_);
v___x_2857_ = lean_box(0);
v___x_2858_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v___x_2856_, v___x_2857_);
v___x_2859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2860_ = l_Lean_MessageData_joinSep(v___x_2858_, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2854_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__14);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___y_2835_ = v___x_2863_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__7);
v___x_2865_ = lean_box(0);
v___x_2866_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2833_, v___x_2865_);
v___x_2867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2868_ = l_Lean_MessageData_joinSep(v___x_2866_, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2864_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___y_2835_ = v___x_2869_;
goto v___jp_2834_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v___x_2848_);
v___x_2870_ = lean_box(0);
v___x_2871_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__2(v_a_2833_, v___x_2870_);
v___x_2872_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__11);
v___x_2873_ = l_Lean_MessageData_joinSep(v___x_2871_, v___x_2872_);
v___y_2835_ = v___x_2873_;
goto v___jp_2834_;
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v___x_2848_);
lean_dec(v_a_2833_);
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__16);
v___y_2835_ = v___x_2874_;
goto v___jp_2834_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__1);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___y_2835_);
v___x_2838_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__5_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__3);
v___x_2841_ = l_Lean_MessageData_ofName(v___x_2803_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___closed__5);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2839_);
v___x_2846_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_a_2802_, v___x_2845_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref(v___x_2846_);
v_a_2796_ = v___x_2806_;
goto v___jp_2795_;
}
else
{
lean_dec(v_decl_2787_);
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v___x_2803_);
lean_dec(v_decl_2787_);
v_a_2875_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2832_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2832_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v___x_2803_);
lean_dec(v_decl_2787_);
v_a_2883_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2804_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2804_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
v___jp_2795_:
{
size_t v___x_2797_; size_t v___x_2798_; 
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2790_, v___x_2797_);
v_i_2790_ = v___x_2798_;
v_b_2791_ = v_a_2796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3___boxed(lean_object* v_decl_2891_, lean_object* v_as_2892_, lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_b_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
size_t v_sz_boxed_2899_; size_t v_i_boxed_2900_; lean_object* v_res_2901_; 
v_sz_boxed_2899_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2900_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2891_, v_as_2892_, v_sz_boxed_2899_, v_i_boxed_2900_, v_b_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec_ref(v_as_2892_);
return v_res_2901_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_2904_ = l_Lean_stringToMessageData(v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(lean_object* v___x_2905_, lean_object* v___x_2906_, lean_object* v___x_2907_, lean_object* v_name_2908_, lean_object* v_decl_2909_, lean_object* v_stx_2910_, uint8_t v_kind_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; uint8_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 0;
v___x_2976_ = l_Lean_instBEqAttributeKind_beq(v_kind_2911_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec(v_stx_2910_);
lean_dec(v_decl_2909_);
lean_dec_ref(v___x_2907_);
lean_dec_ref(v___x_2906_);
lean_dec_ref(v___x_2905_);
v___x_2977_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_2908_, v_kind_2911_, v___y_2912_, v___y_2913_);
return v___x_2977_;
}
else
{
goto v___jp_2949_;
}
v___jp_2915_:
{
lean_object* v___x_2919_; size_t v_sz_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2919_ = lean_box(0);
v_sz_2920_ = lean_array_size(v___y_2916_);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__3(v_decl_2909_, v___y_2916_, v_sz_2920_, v___x_2921_, v___x_2919_, v___y_2917_, v___y_2918_);
lean_dec_ref(v___y_2916_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2930_);
v___x_2924_ = v___x_2922_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v___x_2922_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2919_);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2919_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
return v___x_2922_;
}
}
v___jp_2931_:
{
lean_object* v___x_2935_; lean_object* v_env_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_st_ref_get(v___y_2934_);
v_env_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_ref(v_env_2936_);
lean_dec(v___x_2935_);
lean_inc(v_decl_2909_);
v___x_2937_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_2936_, v_decl_2909_);
if (lean_obj_tag(v___x_2937_) == 1)
{
lean_object* v_val_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec_ref(v___y_2932_);
v_val_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_val_2938_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2940_ = 0;
v___x_2941_ = l_Lean_MessageData_ofConstName(v_decl_2909_, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2939_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_2944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = l_Lean_MessageData_ofConstName(v_val_2938_, v___x_2940_);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2939_);
v___x_2948_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_2910_, v___x_2947_, v___y_2933_, v___y_2934_);
lean_dec(v_stx_2910_);
return v___x_2948_;
}
else
{
lean_dec(v___x_2937_);
lean_dec(v_stx_2910_);
v___y_2916_ = v___y_2932_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
goto v___jp_2915_;
}
}
v___jp_2949_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_2951_ = l_Lean_Name_mkStr4(v___x_2905_, v___x_2906_, v___x_2950_, v___x_2907_);
lean_inc(v_stx_2910_);
v___x_2952_ = l_Lean_Syntax_isOfKind(v_stx_2910_, v___x_2951_);
lean_dec(v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec(v_stx_2910_);
lean_dec(v_decl_2909_);
v___x_2953_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2954_ = l_Lean_MessageData_ofName(v_name_2908_);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_2957_, v___y_2912_, v___y_2913_);
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v_env_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v_tags_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_name_2908_);
v___x_2959_ = lean_st_ref_get(v___y_2913_);
v_env_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc_ref(v_env_2960_);
lean_dec(v___x_2959_);
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = l_Lean_Syntax_getArg(v_stx_2910_, v___x_2961_);
v_tags_2963_ = l_Lean_Syntax_getArgs(v___x_2962_);
lean_dec(v___x_2962_);
v___x_2964_ = 0;
lean_inc(v_decl_2909_);
v___x_2965_ = l_Lean_Environment_find_x3f(v_env_2960_, v_decl_2909_, v___x_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
v___y_2932_ = v_tags_2963_;
v___y_2933_ = v___y_2912_;
v___y_2934_ = v___y_2913_;
goto v___jp_2931_;
}
else
{
lean_dec_ref(v___x_2965_);
if (v___x_2952_ == 0)
{
v___y_2932_ = v_tags_2963_;
v___y_2933_ = v___y_2912_;
v___y_2934_ = v___y_2913_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2966_; lean_object* v_env_2967_; uint8_t v___x_2968_; 
v___x_2966_ = lean_st_ref_get(v___y_2913_);
v_env_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_ref(v_env_2967_);
lean_dec(v___x_2966_);
v___x_2968_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_2967_, v_decl_2909_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref(v_tags_2963_);
v___x_2969_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_2970_ = l_Lean_MessageData_ofConstName(v_decl_2909_, v___x_2964_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_2910_, v___x_2973_, v___y_2912_, v___y_2913_);
lean_dec(v_stx_2910_);
return v___x_2974_;
}
else
{
v___y_2932_ = v_tags_2963_;
v___y_2933_ = v___y_2912_;
v___y_2934_ = v___y_2913_;
goto v___jp_2931_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v___x_2978_, lean_object* v___x_2979_, lean_object* v___x_2980_, lean_object* v_name_2981_, lean_object* v_decl_2982_, lean_object* v_stx_2983_, lean_object* v_kind_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v_kind_boxed_2988_; lean_object* v_res_2989_; 
v_kind_boxed_2988_ = lean_unbox(v_kind_2984_);
v_res_2989_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(v___x_2978_, v___x_2979_, v___x_2980_, v_name_2981_, v_decl_2982_, v_stx_2983_, v_kind_boxed_2988_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_));
v___x_3024_ = l_Lean_registerBuiltinAttribute(v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2____boxed(lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_();
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(lean_object* v_tag_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___redArg(v_tag_3027_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tag_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0(v_tag_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_3037_, lean_object* v_k_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3037_, v_k_3038_, v_x_3039_, v_x_3040_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_3043_, lean_object* v_k_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_tagInfo___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__0_spec__0(v_as_3043_, v_k_3044_, v_x_3045_, v_x_3046_, v_x_3047_);
lean_dec_ref(v_k_3044_);
lean_dec_ref(v_as_3043_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_3049_, size_t v_sz_3050_, size_t v_i_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___redArg(v_as_3049_, v_sz_3050_, v_i_3051_, v_b_3052_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_3057_, lean_object* v_sz_3058_, lean_object* v_i_3059_, lean_object* v_b_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
size_t v_sz_boxed_3064_; size_t v_i_boxed_3065_; lean_object* v_res_3066_; 
v_sz_boxed_3064_ = lean_unbox_usize(v_sz_3058_);
lean_dec(v_sz_3058_);
v_i_boxed_3065_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__2(v_as_3057_, v_sz_boxed_3064_, v_i_boxed_3065_, v_b_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v_as_3057_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_init_3067_, lean_object* v_t_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__4_spec__5(v_init_3067_, v_t_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_n_3070_, lean_object* v_as_3071_, lean_object* v_lo_3072_, lean_object* v_hi_3073_, lean_object* v_w_3074_, lean_object* v_hlo_3075_, lean_object* v_hhi_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___redArg(v_as_3071_, v_lo_3072_, v_hi_3073_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_n_3078_, lean_object* v_as_3079_, lean_object* v_lo_3080_, lean_object* v_hi_3081_, lean_object* v_w_3082_, lean_object* v_hlo_3083_, lean_object* v_hhi_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__5(v_n_3078_, v_as_3079_, v_lo_3080_, v_hi_3081_, v_w_3082_, v_hlo_3083_, v_hhi_3084_);
lean_dec(v_hi_3081_);
lean_dec(v_n_3078_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(lean_object* v_init_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___redArg(v_init_3086_, v_x_3087_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* v_init_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTags___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__spec__1_spec__6(v_init_3092_, v_x_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3100_, lean_object* v_x_3101_){
_start:
{
lean_object* v_fst_3102_; lean_object* v_snd_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_fst_3102_ = lean_ctor_get(v_x_3101_, 0);
lean_inc(v_fst_3102_);
v_snd_3103_ = lean_ctor_get(v_x_3101_, 1);
lean_inc(v_snd_3103_);
lean_dec_ref(v_x_3101_);
v___x_3104_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2845012366____hygCtx___hyg_2__spec__0___redArg(v_es_3100_, v_fst_3102_, v___x_3104_);
v___x_3106_ = lean_array_push(v___x_3105_, v_snd_3103_);
v___x_3107_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3102_, v___x_3106_, v_es_3100_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3108_, lean_object* v_x_3109_){
_start:
{
if (lean_obj_tag(v_x_3109_) == 0)
{
lean_object* v_k_3110_; lean_object* v_v_3111_; lean_object* v_l_3112_; lean_object* v_r_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_k_3110_ = lean_ctor_get(v_x_3109_, 1);
v_v_3111_ = lean_ctor_get(v_x_3109_, 2);
v_l_3112_ = lean_ctor_get(v_x_3109_, 3);
v_r_3113_ = lean_ctor_get(v_x_3109_, 4);
v___x_3114_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3108_, v_l_3112_);
lean_inc(v_v_3111_);
lean_inc(v_k_3110_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_k_3110_);
lean_ctor_set(v___x_3115_, 1, v_v_3111_);
v___x_3116_ = lean_array_push(v___x_3114_, v___x_3115_);
v_init_3108_ = v___x_3116_;
v_x_3109_ = v_r_3113_;
goto _start;
}
else
{
return v_init_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3118_, lean_object* v_x_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3118_, v_x_3119_);
lean_dec(v_x_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3121_, lean_object* v_x2_3122_){
_start:
{
lean_object* v_fst_3123_; lean_object* v_fst_3124_; uint8_t v___x_3125_; 
v_fst_3123_ = lean_ctor_get(v_x1_3121_, 0);
v_fst_3124_ = lean_ctor_get(v_x2_3122_, 0);
v___x_3125_ = l_Lean_Name_quickLt(v_fst_3123_, v_fst_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3126_, lean_object* v_x2_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3126_, v_x2_3127_);
lean_dec_ref(v_x2_3127_);
lean_dec_ref(v_x1_3126_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_3131_, lean_object* v_lo_3132_, lean_object* v_hi_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_nat_dec_lt(v_lo_3132_, v_hi_3133_);
if (v___x_3134_ == 0)
{
lean_dec(v_lo_3132_);
return v_as_3131_;
}
else
{
lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v_fst_3137_; lean_object* v_snd_3138_; uint8_t v___x_3139_; 
v___f_3135_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_3132_);
v___x_3136_ = l_Array_qpartition___redArg(v_as_3131_, v___f_3135_, v_lo_3132_, v_hi_3133_);
v_fst_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_fst_3137_);
v_snd_3138_ = lean_ctor_get(v___x_3136_, 1);
lean_inc(v_snd_3138_);
lean_dec_ref(v___x_3136_);
v___x_3139_ = lean_nat_dec_le(v_hi_3133_, v_fst_3137_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_snd_3138_, v_lo_3132_, v_fst_3137_);
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = lean_nat_add(v_fst_3137_, v___x_3141_);
lean_dec(v_fst_3137_);
v_as_3131_ = v___x_3140_;
v_lo_3132_ = v___x_3142_;
goto _start;
}
else
{
lean_dec(v_fst_3137_);
lean_dec(v_lo_3132_);
return v_snd_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_3144_, lean_object* v_lo_3145_, lean_object* v_hi_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_as_3144_, v_lo_3145_, v_hi_3146_);
lean_dec(v_hi_3146_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_x_3150_, lean_object* v_s_3151_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3154_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3153_, v_s_3151_);
v___x_3160_ = lean_array_get_size(v___x_3154_);
v___x_3161_ = lean_nat_dec_eq(v___x_3160_, v___x_3152_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___y_3165_; uint8_t v___x_3167_; 
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = lean_nat_sub(v___x_3160_, v___x_3162_);
v___x_3167_ = lean_nat_dec_le(v___x_3152_, v___x_3163_);
if (v___x_3167_ == 0)
{
lean_inc(v___x_3163_);
v___y_3165_ = v___x_3163_;
goto v___jp_3164_;
}
else
{
v___y_3165_ = v___x_3152_;
goto v___jp_3164_;
}
v___jp_3164_:
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_nat_dec_le(v___y_3165_, v___x_3163_);
if (v___x_3166_ == 0)
{
lean_dec(v___x_3163_);
lean_inc(v___y_3165_);
v___y_3156_ = v___y_3165_;
v___y_3157_ = v___y_3165_;
goto v___jp_3155_;
}
else
{
v___y_3156_ = v___y_3165_;
v___y_3157_ = v___x_3163_;
goto v___jp_3155_;
}
}
}
else
{
lean_object* v___x_3168_; 
lean_inc_ref_n(v___x_3154_, 2);
v___x_3168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3154_);
lean_ctor_set(v___x_3168_, 1, v___x_3154_);
lean_ctor_set(v___x_3168_, 2, v___x_3154_);
return v___x_3168_;
}
v___jp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3154_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_inc_ref_n(v___x_3158_, 2);
v___x_3159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_x_3169_, lean_object* v_s_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_x_3169_, v_s_3170_);
lean_dec(v_s_3170_);
lean_dec_ref(v_x_3169_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v_es_3172_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3175_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v___x_3174_, v_es_3172_);
v___x_3176_ = lean_array_get_size(v___x_3175_);
v___x_3177_ = lean_nat_dec_eq(v___x_3176_, v___x_3173_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___y_3181_; uint8_t v___x_3185_; 
v___x_3178_ = lean_unsigned_to_nat(1u);
v___x_3179_ = lean_nat_sub(v___x_3176_, v___x_3178_);
v___x_3185_ = lean_nat_dec_le(v___x_3173_, v___x_3179_);
if (v___x_3185_ == 0)
{
lean_inc(v___x_3179_);
v___y_3181_ = v___x_3179_;
goto v___jp_3180_;
}
else
{
v___y_3181_ = v___x_3173_;
goto v___jp_3180_;
}
v___jp_3180_:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_nat_dec_le(v___y_3181_, v___x_3179_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
lean_dec(v___x_3179_);
lean_inc(v___y_3181_);
v___x_3183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3175_, v___y_3181_, v___y_3181_);
lean_dec(v___y_3181_);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; 
v___x_3184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v___x_3175_, v___y_3181_, v___x_3179_);
lean_dec(v___x_3179_);
return v___x_3184_;
}
}
}
else
{
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_es_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v_es_3186_);
lean_dec(v_es_3186_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(lean_object* v___x_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3188_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v___x_3193_, lean_object* v_x_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(v___x_3193_, v_x_3194_, v___y_3195_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v_x_3194_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v___x_3224_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2____boxed(lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_();
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(lean_object* v_init_3227_, lean_object* v_t_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0_spec__0(v_init_3227_, v_t_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3230_, lean_object* v_t_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__0(v_init_3230_, v_t_3231_);
lean_dec(v_t_3231_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(lean_object* v_n_3233_, lean_object* v_as_3234_, lean_object* v_lo_3235_, lean_object* v_hi_3236_, lean_object* v_w_3237_, lean_object* v_hlo_3238_, lean_object* v_hhi_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg(v_as_3234_, v_lo_3235_, v_hi_3236_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3241_, lean_object* v_as_3242_, lean_object* v_lo_3243_, lean_object* v_hi_3244_, lean_object* v_w_3245_, lean_object* v_hlo_3246_, lean_object* v_hhi_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1(v_n_3241_, v_as_3242_, v_lo_3243_, v_hi_3244_, v_w_3245_, v_hlo_3246_, v_hhi_3247_);
lean_dec(v_hi_3244_);
lean_dec(v_n_3241_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(lean_object* v_as_3249_, lean_object* v_k_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_m_3255_; lean_object* v_a_3256_; uint8_t v___x_3257_; 
v___x_3253_ = lean_nat_add(v_x_3251_, v_x_3252_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v_m_3255_ = lean_nat_shiftr(v___x_3253_, v___x_3254_);
lean_dec(v___x_3253_);
v_a_3256_ = lean_array_fget_borrowed(v_as_3249_, v_m_3255_);
v___x_3257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3256_, v_k_3250_);
if (v___x_3257_ == 0)
{
uint8_t v___x_3258_; 
lean_dec(v_x_3252_);
v___x_3258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3250_, v_a_3256_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
lean_dec(v_m_3255_);
lean_dec(v_x_3251_);
lean_inc(v_a_3256_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_a_3256_);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_nat_dec_eq(v_m_3255_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = lean_nat_sub(v_m_3255_, v___x_3254_);
lean_dec(v_m_3255_);
v___x_3263_ = lean_nat_dec_lt(v___x_3262_, v_x_3251_);
if (v___x_3263_ == 0)
{
v_x_3252_ = v___x_3262_;
goto _start;
}
else
{
lean_object* v___x_3265_; 
lean_dec(v___x_3262_);
lean_dec(v_x_3251_);
v___x_3265_ = lean_box(0);
return v___x_3265_;
}
}
else
{
lean_object* v___x_3266_; 
lean_dec(v_m_3255_);
lean_dec(v_x_3251_);
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
}
}
else
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
lean_dec(v_x_3251_);
v___x_3267_ = lean_nat_add(v_m_3255_, v___x_3254_);
lean_dec(v_m_3255_);
v___x_3268_ = lean_nat_dec_le(v___x_3267_, v_x_3252_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
lean_dec(v___x_3267_);
lean_dec(v_x_3252_);
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
else
{
v_x_3251_ = v___x_3267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg___boxed(lean_object* v_as_3271_, lean_object* v_k_3272_, lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3271_, v_k_3272_, v_x_3273_, v_x_3274_);
lean_dec_ref(v_k_3272_);
lean_dec_ref(v_as_3271_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(lean_object* v_tactic_3276_, lean_object* v_as_3277_, size_t v_sz_3278_, size_t v_i_3279_, lean_object* v_b_3280_){
_start:
{
lean_object* v_a_3282_; uint8_t v___x_3286_; 
v___x_3286_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
if (v___x_3286_ == 0)
{
lean_dec(v_tactic_3276_);
return v_b_3280_;
}
else
{
lean_object* v___x_3287_; lean_object* v_a_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3287_ = lean_unsigned_to_nat(0u);
v_a_3288_ = lean_array_uget_borrowed(v_as_3277_, v_i_3279_);
v___x_3289_ = lean_array_get_size(v_a_3288_);
v___x_3290_ = lean_nat_dec_lt(v___x_3287_, v___x_3289_);
if (v___x_3290_ == 0)
{
v_a_3282_ = v_b_3280_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3291_ = lean_unsigned_to_nat(1u);
v___x_3292_ = lean_nat_sub(v___x_3289_, v___x_3291_);
v___x_3293_ = lean_nat_dec_le(v___x_3287_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_dec(v___x_3292_);
v_a_3282_ = v_b_3280_;
goto v___jp_3281_;
}
else
{
lean_object* v_extensions_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_extensions_3294_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
lean_inc(v_tactic_3276_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_tactic_3276_);
lean_ctor_set(v___x_3295_, 1, v_extensions_3294_);
v___x_3296_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_a_3288_, v___x_3295_, v___x_3287_, v___x_3292_);
lean_dec_ref(v___x_3295_);
if (lean_obj_tag(v___x_3296_) == 1)
{
lean_object* v_val_3297_; lean_object* v_snd_3298_; lean_object* v___x_3299_; 
v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_val_3297_);
lean_dec_ref(v___x_3296_);
v_snd_3298_ = lean_ctor_get(v_val_3297_, 1);
lean_inc(v_snd_3298_);
lean_dec(v_val_3297_);
v___x_3299_ = l_Array_append___redArg(v_b_3280_, v_snd_3298_);
lean_dec(v_snd_3298_);
v_a_3282_ = v___x_3299_;
goto v___jp_3281_;
}
else
{
lean_dec(v___x_3296_);
v_a_3282_ = v_b_3280_;
goto v___jp_3281_;
}
}
}
}
v___jp_3281_:
{
size_t v___x_3283_; size_t v___x_3284_; 
v___x_3283_ = ((size_t)1ULL);
v___x_3284_ = lean_usize_add(v_i_3279_, v___x_3283_);
v_i_3279_ = v___x_3284_;
v_b_3280_ = v_a_3282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1___boxed(lean_object* v_tactic_3300_, lean_object* v_as_3301_, lean_object* v_sz_3302_, lean_object* v_i_3303_, lean_object* v_b_3304_){
_start:
{
size_t v_sz_boxed_3305_; size_t v_i_boxed_3306_; lean_object* v_res_3307_; 
v_sz_boxed_3305_ = lean_unbox_usize(v_sz_3302_);
lean_dec(v_sz_3302_);
v_i_boxed_3306_ = lean_unbox_usize(v_i_3303_);
lean_dec(v_i_3303_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3300_, v_as_3301_, v_sz_boxed_3305_, v_i_boxed_3306_, v_b_3304_);
lean_dec_ref(v_as_3301_);
return v_res_3307_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_box(1);
v___x_3309_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object* v_env_3310_, lean_object* v_tactic_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v_toEnvExtension_3313_; lean_object* v_asyncMode_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v_importedEntries_3319_; lean_object* v_extensions_3320_; size_t v_sz_3321_; size_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3312_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_3313_ = lean_ctor_get(v___x_3312_, 0);
v_asyncMode_3314_ = lean_ctor_get(v_toEnvExtension_3313_, 2);
v___x_3315_ = lean_box(1);
v___x_3316_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0, &l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_getTacticExtensions___closed__0);
v___x_3317_ = lean_box(0);
lean_inc_ref(v_env_3310_);
v___x_3318_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3316_, v_toEnvExtension_3313_, v_env_3310_, v_asyncMode_3314_, v___x_3317_);
v_importedEntries_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc_ref(v_importedEntries_3319_);
lean_dec(v___x_3318_);
v_extensions_3320_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0___closed__0_00___x40_Lean_Parser_Tactic_Doc_291731992____hygCtx___hyg_2_));
v_sz_3321_ = lean_array_size(v_importedEntries_3319_);
v___x_3322_ = ((size_t)0ULL);
lean_inc(v_tactic_3311_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__1(v_tactic_3311_, v_importedEntries_3319_, v_sz_3321_, v___x_3322_, v_extensions_3320_);
lean_dec_ref(v_importedEntries_3319_);
v___x_3324_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3315_, v___x_3312_, v_env_3310_, v_asyncMode_3314_, v___x_3317_);
v___x_3325_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3324_, v_tactic_3311_);
lean_dec(v_tactic_3311_);
lean_dec(v___x_3324_);
if (lean_obj_tag(v___x_3325_) == 1)
{
lean_object* v_val_3326_; lean_object* v___x_3327_; 
v_val_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_val_3326_);
lean_dec_ref(v___x_3325_);
v___x_3327_ = l_Array_append___redArg(v___x_3323_, v_val_3326_);
lean_dec(v_val_3326_);
return v___x_3327_;
}
else
{
lean_dec(v___x_3325_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(lean_object* v_as_3328_, lean_object* v_k_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___redArg(v_as_3328_, v_k_3329_, v_x_3330_, v_x_3331_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0___boxed(lean_object* v_as_3334_, lean_object* v_k_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_getTacticExtensions_spec__0(v_as_3334_, v_k_3335_, v_x_3336_, v_x_3337_, v_x_3338_);
lean_dec_ref(v_k_3335_);
lean_dec_ref(v_as_3334_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(lean_object* v_s_3340_, lean_object* v_pos_3341_){
_start:
{
lean_object* v_str_3342_; lean_object* v_startInclusive_3343_; lean_object* v_endExclusive_3344_; lean_object* v___x_3345_; uint8_t v___y_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_str_3342_ = lean_ctor_get(v_s_3340_, 0);
v_startInclusive_3343_ = lean_ctor_get(v_s_3340_, 1);
v_endExclusive_3344_ = lean_ctor_get(v_s_3340_, 2);
v___x_3345_ = lean_nat_add(v_startInclusive_3343_, v_pos_3341_);
v___x_3354_ = lean_unsigned_to_nat(0u);
v___x_3355_ = lean_nat_sub(v_endExclusive_3344_, v___x_3345_);
v___x_3356_ = lean_nat_dec_eq(v___x_3354_, v___x_3355_);
lean_dec(v___x_3355_);
if (v___x_3356_ == 0)
{
uint32_t v___x_3357_; uint8_t v___y_3359_; uint32_t v___x_3364_; uint8_t v___x_3365_; 
v___x_3357_ = lean_string_utf8_get_fast(v_str_3342_, v___x_3345_);
v___x_3364_ = 32;
v___x_3365_ = lean_uint32_dec_eq(v___x_3357_, v___x_3364_);
if (v___x_3365_ == 0)
{
uint32_t v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = 9;
v___x_3367_ = lean_uint32_dec_eq(v___x_3357_, v___x_3366_);
v___y_3359_ = v___x_3367_;
goto v___jp_3358_;
}
else
{
v___y_3359_ = v___x_3365_;
goto v___jp_3358_;
}
v___jp_3358_:
{
if (v___y_3359_ == 0)
{
uint32_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = 13;
v___x_3361_ = lean_uint32_dec_eq(v___x_3357_, v___x_3360_);
if (v___x_3361_ == 0)
{
uint32_t v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = 10;
v___x_3363_ = lean_uint32_dec_eq(v___x_3357_, v___x_3362_);
v___y_3353_ = v___x_3363_;
goto v___jp_3352_;
}
else
{
v___y_3353_ = v___x_3361_;
goto v___jp_3352_;
}
}
else
{
goto v___jp_3346_;
}
}
}
else
{
lean_dec(v___x_3345_);
return v_pos_3341_;
}
v___jp_3346_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3347_ = lean_string_utf8_next_fast(v_str_3342_, v___x_3345_);
v___x_3348_ = lean_nat_sub(v___x_3347_, v___x_3345_);
lean_dec(v___x_3345_);
v___x_3349_ = lean_nat_add(v_pos_3341_, v___x_3348_);
lean_dec(v___x_3348_);
v___x_3350_ = lean_nat_dec_lt(v_pos_3341_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_dec(v___x_3349_);
return v_pos_3341_;
}
else
{
lean_dec(v_pos_3341_);
v_pos_3341_ = v___x_3349_;
goto _start;
}
}
v___jp_3352_:
{
if (v___y_3353_ == 0)
{
lean_dec(v___x_3345_);
return v_pos_3341_;
}
else
{
goto v___jp_3346_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0___boxed(lean_object* v_s_3368_, lean_object* v_pos_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_s_3368_, v_pos_3369_);
lean_dec_ref(v_s_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(lean_object* v_str_3373_){
_start:
{
lean_object* v___y_3375_; lean_object* v_str_3378_; lean_object* v_startInclusive_3379_; lean_object* v_endExclusive_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_str_3378_ = lean_ctor_get(v_str_3373_, 0);
v_startInclusive_3379_ = lean_ctor_get(v_str_3373_, 1);
v_endExclusive_3380_ = lean_ctor_get(v_str_3373_, 2);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine_spec__0(v_str_3373_, v___x_3381_);
v___x_3383_ = lean_nat_sub(v_endExclusive_3380_, v_startInclusive_3379_);
v___x_3384_ = lean_nat_dec_eq(v___x_3382_, v___x_3383_);
lean_dec(v___x_3383_);
lean_dec(v___x_3382_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__1));
v___x_3386_ = lean_string_utf8_extract(v_str_3378_, v_startInclusive_3379_, v_endExclusive_3380_);
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___y_3375_ = v___x_3387_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_string_utf8_extract(v_str_3378_, v_startInclusive_3379_, v_endExclusive_3380_);
v___y_3375_ = v___x_3388_;
goto v___jp_3374_;
}
v___jp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3377_ = lean_string_append(v___y_3375_, v___x_3376_);
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___boxed(lean_object* v_str_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_str_3389_);
lean_dec_ref(v_str_3389_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(lean_object* v_s_3393_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___closed__0));
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0___boxed(lean_object* v_s_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v_s_3395_);
lean_dec_ref(v_s_3395_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(lean_object* v_str_3397_, lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v_a_3400_, lean_object* v_b_3401_){
_start:
{
lean_object* v_it_3403_; lean_object* v_startInclusive_3404_; lean_object* v_endExclusive_3405_; 
if (lean_obj_tag(v_a_3400_) == 0)
{
lean_object* v_currPos_3409_; lean_object* v_searcher_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3436_; 
v_currPos_3409_ = lean_ctor_get(v_a_3400_, 0);
v_searcher_3410_ = lean_ctor_get(v_a_3400_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_a_3400_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3412_ = v_a_3400_;
v_isShared_3413_ = v_isSharedCheck_3436_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_searcher_3410_);
lean_inc(v_currPos_3409_);
lean_dec(v_a_3400_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3436_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_startInclusive_3414_; lean_object* v_endExclusive_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_startInclusive_3414_ = lean_ctor_get(v___x_3398_, 1);
v_endExclusive_3415_ = lean_ctor_get(v___x_3398_, 2);
v___x_3416_ = lean_nat_sub(v_endExclusive_3415_, v_startInclusive_3414_);
v___x_3417_ = lean_nat_dec_eq(v_searcher_3410_, v___x_3416_);
lean_dec(v___x_3416_);
if (v___x_3417_ == 0)
{
uint32_t v___x_3418_; uint32_t v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = 10;
v___x_3419_ = lean_string_utf8_get_fast(v_str_3397_, v_searcher_3410_);
v___x_3420_ = lean_uint32_dec_eq(v___x_3419_, v___x_3418_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3421_ = lean_string_utf8_next_fast(v_str_3397_, v_searcher_3410_);
lean_dec(v_searcher_3410_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v___x_3421_);
v___x_3423_ = v___x_3412_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_currPos_3409_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
v_a_3400_ = v___x_3423_;
goto _start;
}
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v_slice_3429_; lean_object* v_nextIt_3431_; 
v___x_3426_ = lean_string_utf8_next_fast(v_str_3397_, v_searcher_3410_);
v___x_3427_ = lean_nat_sub(v___x_3426_, v_searcher_3410_);
v___x_3428_ = lean_nat_add(v_searcher_3410_, v___x_3427_);
lean_dec(v___x_3427_);
v_slice_3429_ = l_String_Slice_subslice_x21(v___x_3398_, v_currPos_3409_, v_searcher_3410_);
lean_inc(v___x_3428_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v___x_3428_);
lean_ctor_set(v___x_3412_, 0, v___x_3428_);
v_nextIt_3431_ = v___x_3412_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v___x_3428_);
v_nextIt_3431_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v_startInclusive_3432_; lean_object* v_endExclusive_3433_; 
v_startInclusive_3432_ = lean_ctor_get(v_slice_3429_, 0);
lean_inc(v_startInclusive_3432_);
v_endExclusive_3433_ = lean_ctor_get(v_slice_3429_, 1);
lean_inc(v_endExclusive_3433_);
lean_dec_ref(v_slice_3429_);
v_it_3403_ = v_nextIt_3431_;
v_startInclusive_3404_ = v_startInclusive_3432_;
v_endExclusive_3405_ = v_endExclusive_3433_;
goto v___jp_3402_;
}
}
}
else
{
lean_object* v___x_3435_; 
lean_del_object(v___x_3412_);
lean_dec(v_searcher_3410_);
v___x_3435_ = lean_box(1);
lean_inc(v___x_3399_);
v_it_3403_ = v___x_3435_;
v_startInclusive_3404_ = v_currPos_3409_;
v_endExclusive_3405_ = v___x_3399_;
goto v___jp_3402_;
}
}
}
else
{
lean_dec(v___x_3399_);
lean_dec_ref(v_str_3397_);
return v_b_3401_;
}
v___jp_3402_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_inc_ref(v_str_3397_);
v___x_3406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3406_, 0, v_str_3397_);
lean_ctor_set(v___x_3406_, 1, v_startInclusive_3404_);
lean_ctor_set(v___x_3406_, 2, v_endExclusive_3405_);
v___x_3407_ = lean_array_push(v_b_3401_, v___x_3406_);
v_a_3400_ = v_it_3403_;
v_b_3401_ = v___x_3407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg___boxed(lean_object* v_str_3437_, lean_object* v___x_3438_, lean_object* v___x_3439_, lean_object* v_a_3440_, lean_object* v_b_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3437_, v___x_3438_, v___x_3439_, v_a_3440_, v_b_3441_);
lean_dec_ref(v___x_3438_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(lean_object* v_x_3443_, lean_object* v_x_3444_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 0)
{
return v_x_3443_;
}
else
{
lean_object* v_head_3445_; lean_object* v_tail_3446_; lean_object* v___x_3447_; 
v_head_3445_ = lean_ctor_get(v_x_3444_, 0);
v_tail_3446_ = lean_ctor_get(v_x_3444_, 1);
v___x_3447_ = lean_string_append(v_x_3443_, v_head_3445_);
v_x_3443_ = v___x_3447_;
v_x_3444_ = v_tail_3446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3___boxed(lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v_x_3449_, v_x_3450_);
lean_dec(v_x_3450_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
if (lean_obj_tag(v_a_3452_) == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = l_List_reverse___redArg(v_a_3453_);
return v___x_3454_;
}
else
{
lean_object* v_head_3455_; lean_object* v_tail_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3465_; 
v_head_3455_ = lean_ctor_get(v_a_3452_, 0);
v_tail_3456_ = lean_ctor_get(v_a_3452_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3458_ = v_a_3452_;
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_tail_3456_);
lean_inc(v_head_3455_);
lean_dec(v_a_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine(v_head_3455_);
lean_dec(v_head_3455_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3453_);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3453_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3452_ = v_tail_3456_;
v_a_3453_ = v___x_3462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(lean_object* v_str_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v_lines_3477_; 
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_string_utf8_byte_size(v_str_3470_);
lean_inc_ref(v_str_3470_);
v___x_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3473_, 0, v_str_3470_);
lean_ctor_set(v___x_3473_, 1, v___x_3471_);
lean_ctor_set(v___x_3473_, 2, v___x_3472_);
v___x_3474_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__0(v___x_3473_);
v___x_3475_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__0));
v___x_3476_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3470_, v___x_3473_, v___x_3472_, v___x_3474_, v___x_3475_);
lean_dec_ref(v___x_3473_);
v_lines_3477_ = lean_array_to_list(v___x_3476_);
if (lean_obj_tag(v_lines_3477_) == 0)
{
lean_object* v___x_3478_; 
v___x_3478_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3478_;
}
else
{
lean_object* v_tail_3479_; 
v_tail_3479_ = lean_ctor_get(v_lines_3477_, 1);
lean_inc(v_tail_3479_);
if (lean_obj_tag(v_tail_3479_) == 0)
{
lean_object* v_head_3480_; lean_object* v_str_3481_; lean_object* v_startInclusive_3482_; lean_object* v_endExclusive_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_head_3480_ = lean_ctor_get(v_lines_3477_, 0);
lean_inc(v_head_3480_);
lean_dec_ref(v_lines_3477_);
v_str_3481_ = lean_ctor_get(v_head_3480_, 0);
lean_inc_ref(v_str_3481_);
v_startInclusive_3482_ = lean_ctor_get(v_head_3480_, 1);
lean_inc(v_startInclusive_3482_);
v_endExclusive_3483_ = lean_ctor_get(v_head_3480_, 2);
lean_inc(v_endExclusive_3483_);
lean_dec(v_head_3480_);
v___x_3484_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3485_ = lean_string_utf8_extract(v_str_3481_, v_startInclusive_3482_, v_endExclusive_3483_);
lean_dec(v_endExclusive_3483_);
lean_dec(v_startInclusive_3482_);
lean_dec_ref(v_str_3481_);
v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3488_ = lean_string_append(v___x_3486_, v___x_3487_);
return v___x_3488_;
}
else
{
lean_object* v_head_3489_; lean_object* v_str_3490_; lean_object* v_startInclusive_3491_; lean_object* v_endExclusive_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_head_3489_ = lean_ctor_get(v_lines_3477_, 0);
lean_inc(v_head_3489_);
lean_dec_ref(v_lines_3477_);
v_str_3490_ = lean_ctor_get(v_head_3489_, 0);
lean_inc_ref(v_str_3490_);
v_startInclusive_3491_ = lean_ctor_get(v_head_3489_, 1);
lean_inc(v_startInclusive_3491_);
v_endExclusive_3492_ = lean_ctor_get(v_head_3489_, 2);
lean_inc(v_endExclusive_3492_);
lean_dec(v_head_3489_);
v___x_3493_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__1));
v___x_3494_ = lean_string_utf8_extract(v_str_3490_, v_startInclusive_3491_, v_endExclusive_3492_);
lean_dec(v_endExclusive_3492_);
lean_dec(v_startInclusive_3491_);
lean_dec_ref(v_str_3490_);
v___x_3495_ = lean_string_append(v___x_3493_, v___x_3494_);
lean_dec_ref(v___x_3494_);
v___x_3496_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_indentLine___closed__0));
v___x_3497_ = lean_string_append(v___x_3495_, v___x_3496_);
v___x_3498_ = lean_box(0);
v___x_3499_ = l_List_mapTR_loop___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__2(v_tail_3479_, v___x_3498_);
v___x_3500_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3501_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3500_, v___x_3499_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_string_append(v___x_3497_, v___x_3501_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet___closed__2));
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(lean_object* v_str_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v_inst_3508_, lean_object* v_R_3509_, lean_object* v_a_3510_, lean_object* v_b_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___redArg(v_str_3505_, v___x_3506_, v___x_3507_, v_a_3510_, v_b_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1___boxed(lean_object* v_str_3513_, lean_object* v___x_3514_, lean_object* v___x_3515_, lean_object* v_inst_3516_, lean_object* v_R_3517_, lean_object* v_a_3518_, lean_object* v_b_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__1(v_str_3513_, v___x_3514_, v___x_3515_, v_inst_3516_, v_R_3517_, v_a_3518_, v_b_3519_);
lean_dec_ref(v___x_3514_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
if (lean_obj_tag(v_a_3521_) == 0)
{
lean_object* v___x_3523_; 
v___x_3523_ = l_List_reverse___redArg(v_a_3522_);
return v___x_3523_;
}
else
{
lean_object* v_head_3524_; lean_object* v_tail_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3534_; 
v_head_3524_ = lean_ctor_get(v_a_3521_, 0);
v_tail_3525_ = lean_ctor_get(v_a_3521_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3527_ = v_a_3521_;
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_tail_3525_);
lean_inc(v_head_3524_);
lean_dec(v_a_3521_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet(v_head_3524_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v_a_3522_);
lean_ctor_set(v___x_3527_, 0, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_a_3522_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3521_ = v_tail_3525_;
v_a_3522_ = v___x_3531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(lean_object* v_s_3535_, lean_object* v_pos_3536_){
_start:
{
lean_object* v_str_3537_; lean_object* v_startInclusive_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_str_3537_ = lean_ctor_get(v_s_3535_, 0);
v_startInclusive_3538_ = lean_ctor_get(v_s_3535_, 1);
v___x_3539_ = lean_nat_add(v_startInclusive_3538_, v_pos_3536_);
v___x_3540_ = lean_nat_sub(v___x_3539_, v_startInclusive_3538_);
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = lean_nat_dec_eq(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___y_3551_; lean_object* v___x_3552_; uint32_t v___x_3553_; uint8_t v___y_3555_; uint32_t v___x_3560_; uint8_t v___x_3561_; 
lean_inc(v_startInclusive_3538_);
lean_inc_ref(v_str_3537_);
v___x_3543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3543_, 0, v_str_3537_);
lean_ctor_set(v___x_3543_, 1, v_startInclusive_3538_);
lean_ctor_set(v___x_3543_, 2, v___x_3539_);
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3545_ = lean_nat_sub(v___x_3540_, v___x_3544_);
lean_dec(v___x_3540_);
v___x_3546_ = l_String_Slice_posLE(v___x_3543_, v___x_3545_);
lean_dec_ref(v___x_3543_);
v___x_3552_ = lean_nat_add(v_startInclusive_3538_, v___x_3546_);
v___x_3553_ = lean_string_utf8_get_fast(v_str_3537_, v___x_3552_);
lean_dec(v___x_3552_);
v___x_3560_ = 32;
v___x_3561_ = lean_uint32_dec_eq(v___x_3553_, v___x_3560_);
if (v___x_3561_ == 0)
{
uint32_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = 9;
v___x_3563_ = lean_uint32_dec_eq(v___x_3553_, v___x_3562_);
v___y_3555_ = v___x_3563_;
goto v___jp_3554_;
}
else
{
v___y_3555_ = v___x_3561_;
goto v___jp_3554_;
}
v___jp_3547_:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_lt(v___x_3546_, v_pos_3536_);
if (v___x_3548_ == 0)
{
lean_dec(v___x_3546_);
return v_pos_3536_;
}
else
{
lean_dec(v_pos_3536_);
v_pos_3536_ = v___x_3546_;
goto _start;
}
}
v___jp_3550_:
{
if (v___y_3551_ == 0)
{
lean_dec(v___x_3546_);
return v_pos_3536_;
}
else
{
goto v___jp_3547_;
}
}
v___jp_3554_:
{
if (v___y_3555_ == 0)
{
uint32_t v___x_3556_; uint8_t v___x_3557_; 
v___x_3556_ = 13;
v___x_3557_ = lean_uint32_dec_eq(v___x_3553_, v___x_3556_);
if (v___x_3557_ == 0)
{
uint32_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = 10;
v___x_3559_ = lean_uint32_dec_eq(v___x_3553_, v___x_3558_);
v___y_3551_ = v___x_3559_;
goto v___jp_3550_;
}
else
{
v___y_3551_ = v___x_3557_;
goto v___jp_3550_;
}
}
else
{
goto v___jp_3547_;
}
}
}
else
{
lean_dec(v___x_3540_);
lean_dec(v___x_3539_);
return v_pos_3536_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1___boxed(lean_object* v_s_3564_, lean_object* v_pos_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v_s_3564_, v_pos_3565_);
lean_dec_ref(v_s_3564_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object* v_env_3568_, lean_object* v_tactic_3569_){
_start:
{
lean_object* v_exts_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v_exts_3570_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3568_, v_tactic_3569_);
v___x_3571_ = lean_array_get_size(v_exts_3570_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3573_ = lean_nat_dec_eq(v___x_3571_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3574_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_getTacticExtensionString___closed__0));
v___x_3575_ = lean_array_to_list(v_exts_3570_);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_List_mapTR_loop___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__0(v___x_3575_, v___x_3576_);
v___x_3578_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3579_ = l_List_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_getTacticExtensionString_bullet_spec__3(v___x_3578_, v___x_3577_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_string_append(v___x_3574_, v___x_3579_);
lean_dec_ref(v___x_3579_);
v___x_3581_ = lean_string_utf8_byte_size(v___x_3580_);
lean_inc_ref(v___x_3580_);
v___x_3582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3572_);
lean_ctor_set(v___x_3582_, 2, v___x_3581_);
v___x_3583_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Parser_Tactic_Doc_getTacticExtensionString_spec__1(v___x_3582_, v___x_3581_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = lean_string_utf8_extract(v___x_3580_, v___x_3572_, v___x_3583_);
lean_dec(v___x_3583_);
lean_dec_ref(v___x_3580_);
return v___x_3584_;
}
else
{
lean_object* v___x_3585_; 
lean_dec_ref(v_exts_3570_);
v___x_3585_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_as_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v___x_3590_; 
v_fst_3588_ = lean_ctor_get(v_x_3587_, 0);
lean_inc(v_fst_3588_);
v_snd_3589_ = lean_ctor_get(v_x_3587_, 1);
lean_inc(v_snd_3589_);
lean_dec_ref(v_x_3587_);
v___x_3590_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3588_, v_snd_3589_, v_as_3586_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v_k_3593_; lean_object* v_v_3594_; lean_object* v_l_3595_; lean_object* v_r_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_k_3593_ = lean_ctor_get(v_x_3592_, 1);
v_v_3594_ = lean_ctor_get(v_x_3592_, 2);
v_l_3595_ = lean_ctor_get(v_x_3592_, 3);
v_r_3596_ = lean_ctor_get(v_x_3592_, 4);
v___x_3597_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3591_, v_l_3595_);
lean_inc(v_v_3594_);
lean_inc(v_k_3593_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_k_3593_);
lean_ctor_set(v___x_3598_, 1, v_v_3594_);
v___x_3599_ = lean_array_push(v___x_3597_, v___x_3598_);
v_init_3591_ = v___x_3599_;
v_x_3592_ = v_r_3596_;
goto _start;
}
else
{
return v_init_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3601_, lean_object* v_x_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3601_, v_x_3602_);
lean_dec(v_x_3602_);
return v_res_3603_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_x1_3604_, lean_object* v_x2_3605_){
_start:
{
lean_object* v_fst_3606_; lean_object* v_fst_3607_; uint8_t v___x_3608_; 
v_fst_3606_ = lean_ctor_get(v_x1_3604_, 0);
v_fst_3607_ = lean_ctor_get(v_x2_3605_, 0);
v___x_3608_ = l_Lean_Name_quickLt(v_fst_3606_, v_fst_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(lean_object* v_x1_3609_, lean_object* v_x2_3610_){
_start:
{
uint8_t v_res_3611_; lean_object* v_r_3612_; 
v_res_3611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_x1_3609_, v_x2_3610_);
lean_dec_ref(v_x2_3610_);
lean_dec_ref(v_x1_3609_);
v_r_3612_ = lean_box(v_res_3611_);
return v_r_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_3614_, lean_object* v_lo_3615_, lean_object* v_hi_3616_){
_start:
{
uint8_t v___x_3617_; 
v___x_3617_ = lean_nat_dec_lt(v_lo_3615_, v_hi_3616_);
if (v___x_3617_ == 0)
{
lean_dec(v_lo_3615_);
return v_as_3614_;
}
else
{
lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v_fst_3620_; lean_object* v_snd_3621_; uint8_t v___x_3622_; 
v___f_3618_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_3615_);
v___x_3619_ = l_Array_qpartition___redArg(v_as_3614_, v___f_3618_, v_lo_3615_, v_hi_3616_);
v_fst_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_fst_3620_);
v_snd_3621_ = lean_ctor_get(v___x_3619_, 1);
lean_inc(v_snd_3621_);
lean_dec_ref(v___x_3619_);
v___x_3622_ = lean_nat_dec_le(v_hi_3616_, v_fst_3620_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_snd_3621_, v_lo_3615_, v_fst_3620_);
v___x_3624_ = lean_unsigned_to_nat(1u);
v___x_3625_ = lean_nat_add(v_fst_3620_, v___x_3624_);
lean_dec(v_fst_3620_);
v_as_3614_ = v___x_3623_;
v_lo_3615_ = v___x_3625_;
goto _start;
}
else
{
lean_dec(v_fst_3620_);
lean_dec(v_lo_3615_);
return v_snd_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_3627_, lean_object* v_lo_3628_, lean_object* v_hi_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_as_3627_, v_lo_3628_, v_hi_3629_);
lean_dec(v_hi_3629_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_x_3633_, lean_object* v_s_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3637_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3636_, v_s_3634_);
v___x_3643_ = lean_array_get_size(v___x_3637_);
v___x_3644_ = lean_nat_dec_eq(v___x_3643_, v___x_3635_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___y_3648_; uint8_t v___x_3650_; 
v___x_3645_ = lean_unsigned_to_nat(1u);
v___x_3646_ = lean_nat_sub(v___x_3643_, v___x_3645_);
v___x_3650_ = lean_nat_dec_le(v___x_3635_, v___x_3646_);
if (v___x_3650_ == 0)
{
lean_inc(v___x_3646_);
v___y_3648_ = v___x_3646_;
goto v___jp_3647_;
}
else
{
v___y_3648_ = v___x_3635_;
goto v___jp_3647_;
}
v___jp_3647_:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_nat_dec_le(v___y_3648_, v___x_3646_);
if (v___x_3649_ == 0)
{
lean_dec(v___x_3646_);
lean_inc(v___y_3648_);
v___y_3639_ = v___y_3648_;
v___y_3640_ = v___y_3648_;
goto v___jp_3638_;
}
else
{
v___y_3639_ = v___y_3648_;
v___y_3640_ = v___x_3646_;
goto v___jp_3638_;
}
}
}
else
{
lean_object* v___x_3651_; 
lean_inc_ref_n(v___x_3637_, 2);
v___x_3651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3637_);
lean_ctor_set(v___x_3651_, 1, v___x_3637_);
lean_ctor_set(v___x_3651_, 2, v___x_3637_);
return v___x_3651_;
}
v___jp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3637_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_inc_ref_n(v___x_3641_, 2);
v___x_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
lean_ctor_set(v___x_3642_, 2, v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_x_3652_, lean_object* v_s_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_x_3652_, v_s_3653_);
lean_dec(v_s_3653_);
lean_dec_ref(v_x_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v_es_3655_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3656_ = lean_unsigned_to_nat(0u);
v___x_3657_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3658_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v___x_3657_, v_es_3655_);
v___x_3659_ = lean_array_get_size(v___x_3658_);
v___x_3660_ = lean_nat_dec_eq(v___x_3659_, v___x_3656_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___y_3664_; uint8_t v___x_3668_; 
v___x_3661_ = lean_unsigned_to_nat(1u);
v___x_3662_ = lean_nat_sub(v___x_3659_, v___x_3661_);
v___x_3668_ = lean_nat_dec_le(v___x_3656_, v___x_3662_);
if (v___x_3668_ == 0)
{
lean_inc(v___x_3662_);
v___y_3664_ = v___x_3662_;
goto v___jp_3663_;
}
else
{
v___y_3664_ = v___x_3656_;
goto v___jp_3663_;
}
v___jp_3663_:
{
uint8_t v___x_3665_; 
v___x_3665_ = lean_nat_dec_le(v___y_3664_, v___x_3662_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; 
lean_dec(v___x_3662_);
lean_inc(v___y_3664_);
v___x_3666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3658_, v___y_3664_, v___y_3664_);
lean_dec(v___y_3664_);
return v___x_3666_;
}
else
{
lean_object* v___x_3667_; 
v___x_3667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v___x_3658_, v___y_3664_, v___x_3662_);
lean_dec(v___x_3662_);
return v___x_3667_;
}
}
}
else
{
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_es_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__3_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v_es_3669_);
lean_dec(v_es_3669_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(lean_object* v___x_3671_, lean_object* v_x_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3671_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v___x_3676_, lean_object* v_x_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__4_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(v___x_3676_, v_x_3677_, v___y_3678_);
lean_dec_ref(v___y_3678_);
lean_dec_ref(v_x_3677_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_));
v___x_3707_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2____boxed(lean_object* v_a_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2_();
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(lean_object* v_init_3710_, lean_object* v_t_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0_spec__0(v_init_3710_, v_t_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3713_, lean_object* v_t_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__0(v_init_3713_, v_t_3714_);
lean_dec(v_t_3714_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(lean_object* v_n_3716_, lean_object* v_as_3717_, lean_object* v_lo_3718_, lean_object* v_hi_3719_, lean_object* v_w_3720_, lean_object* v_hlo_3721_, lean_object* v_hhi_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg(v_as_3717_, v_lo_3718_, v_hi_3719_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_3724_, lean_object* v_as_3725_, lean_object* v_lo_3726_, lean_object* v_hi_3727_, lean_object* v_w_3728_, lean_object* v_hlo_3729_, lean_object* v_hhi_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1(v_n_3724_, v_as_3725_, v_lo_3726_, v_hi_3727_, v_w_3728_, v_hlo_3729_, v_hhi_3730_);
lean_dec(v_hi_3727_);
lean_dec(v_n_3724_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1(lean_object* v_tac_3733_, lean_object* v___x_3734_, lean_object* v_toPure_3735_, lean_object* v___f_3736_, lean_object* v_env_3737_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3737_, v_tac_3733_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; lean_object* v_toEnvExtension_3743_; lean_object* v_asyncMode_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_dec_ref(v___f_3736_);
v___x_3742_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3743_ = lean_ctor_get(v___x_3742_, 0);
v_asyncMode_3744_ = lean_ctor_get(v_toEnvExtension_3743_, 2);
v___x_3745_ = lean_box(0);
v___x_3746_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3734_, v___x_3742_, v_env_3737_, v_asyncMode_3744_, v___x_3745_);
v___x_3747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3746_, v_tac_3733_);
lean_dec(v_tac_3733_);
lean_dec(v___x_3746_);
v___x_3748_ = lean_apply_2(v_toPure_3735_, lean_box(0), v___x_3747_);
return v___x_3748_;
}
else
{
lean_object* v_val_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v_val_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_val_3749_);
lean_dec_ref(v___x_3741_);
v___x_3750_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3751_ = 0;
v___x_3752_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3734_, v___x_3750_, v_env_3737_, v_val_3749_, v___x_3751_);
lean_dec(v_val_3749_);
lean_dec_ref(v_env_3737_);
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = lean_array_get_size(v___x_3752_);
v___x_3755_ = lean_nat_dec_lt(v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___f_3736_);
lean_dec(v_tac_3733_);
goto v___jp_3738_;
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
v___x_3757_ = lean_nat_sub(v___x_3754_, v___x_3756_);
v___x_3758_ = lean_nat_dec_le(v___x_3753_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_dec(v___x_3757_);
lean_dec_ref(v___x_3752_);
lean_dec_ref(v___f_3736_);
lean_dec(v_tac_3733_);
goto v___jp_3738_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3759_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v_tac_3733_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1___closed__0));
v___x_3762_ = l_Array_binSearchAux___redArg(v___f_3736_, v___x_3761_, v___x_3752_, v___x_3760_, v___x_3753_, v___x_3757_);
lean_dec_ref(v___x_3752_);
if (lean_obj_tag(v___x_3762_) == 0)
{
goto v___jp_3738_;
}
else
{
lean_object* v_val_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3772_; 
v_val_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3772_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_val_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3772_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v_snd_3767_; lean_object* v___x_3769_; 
v_snd_3767_ = lean_ctor_get(v_val_3763_, 1);
lean_inc(v_snd_3767_);
lean_dec(v_val_3763_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v_snd_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_snd_3767_);
v___x_3769_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_apply_2(v_toPure_3735_, lean_box(0), v___x_3769_);
return v___x_3770_;
}
}
}
}
}
}
v___jp_3738_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_box(0);
v___x_3740_ = lean_apply_2(v_toPure_3735_, lean_box(0), v___x_3739_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object* v_inst_3773_, lean_object* v_inst_3774_, lean_object* v_tac_3775_){
_start:
{
lean_object* v_toApplicative_3776_; lean_object* v_toBind_3777_; lean_object* v_getEnv_3778_; lean_object* v_toPure_3779_; lean_object* v___f_3780_; lean_object* v___x_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; 
v_toApplicative_3776_ = lean_ctor_get(v_inst_3773_, 0);
lean_inc_ref(v_toApplicative_3776_);
v_toBind_3777_ = lean_ctor_get(v_inst_3773_, 1);
lean_inc(v_toBind_3777_);
lean_dec_ref(v_inst_3773_);
v_getEnv_3778_ = lean_ctor_get(v_inst_3774_, 0);
lean_inc(v_getEnv_3778_);
lean_dec_ref(v_inst_3774_);
v_toPure_3779_ = lean_ctor_get(v_toApplicative_3776_, 1);
lean_inc(v_toPure_3779_);
lean_dec_ref(v_toApplicative_3776_);
v___f_3780_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_3781_ = lean_box(1);
v___f_3782_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_Doc_customTacticName___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3782_, 0, v_tac_3775_);
lean_closure_set(v___f_3782_, 1, v___x_3781_);
lean_closure_set(v___f_3782_, 2, v_toPure_3779_);
lean_closure_set(v___f_3782_, 3, v___f_3780_);
v___x_3783_ = lean_apply_4(v_toBind_3777_, lean_box(0), lean_box(0), v_getEnv_3778_, v___f_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName(lean_object* v_m_3784_, lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_tac_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_3785_, v_inst_3786_, v_tac_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_3789_, lean_object* v_k_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v_m_3795_; lean_object* v_a_3796_; uint8_t v___x_3797_; 
v___x_3793_ = lean_nat_add(v_x_3791_, v_x_3792_);
v___x_3794_ = lean_unsigned_to_nat(1u);
v_m_3795_ = lean_nat_shiftr(v___x_3793_, v___x_3794_);
lean_dec(v___x_3793_);
v_a_3796_ = lean_array_fget_borrowed(v_as_3789_, v_m_3795_);
v___x_3797_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3796_, v_k_3790_);
if (v___x_3797_ == 0)
{
uint8_t v___x_3798_; 
lean_dec(v_x_3792_);
v___x_3798_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_754966946____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3790_, v_a_3796_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_m_3795_);
lean_dec(v_x_3791_);
lean_inc(v_a_3796_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_a_3796_);
return v___x_3799_;
}
else
{
lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = lean_unsigned_to_nat(0u);
v___x_3801_ = lean_nat_dec_eq(v_m_3795_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = lean_nat_sub(v_m_3795_, v___x_3794_);
lean_dec(v_m_3795_);
v___x_3803_ = lean_nat_dec_lt(v___x_3802_, v_x_3791_);
if (v___x_3803_ == 0)
{
v_x_3792_ = v___x_3802_;
goto _start;
}
else
{
lean_object* v___x_3805_; 
lean_dec(v___x_3802_);
lean_dec(v_x_3791_);
v___x_3805_ = lean_box(0);
return v___x_3805_;
}
}
else
{
lean_object* v___x_3806_; 
lean_dec(v_m_3795_);
lean_dec(v_x_3791_);
v___x_3806_ = lean_box(0);
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3807_; uint8_t v___x_3808_; 
lean_dec(v_x_3791_);
v___x_3807_ = lean_nat_add(v_m_3795_, v___x_3794_);
lean_dec(v_m_3795_);
v___x_3808_ = lean_nat_dec_le(v___x_3807_, v_x_3792_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
lean_dec(v___x_3807_);
lean_dec(v_x_3792_);
v___x_3809_ = lean_box(0);
return v___x_3809_;
}
else
{
v_x_3791_ = v___x_3807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_3811_, lean_object* v_k_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_3811_, v_k_3812_, v_x_3813_, v_x_3814_);
lean_dec_ref(v_k_3812_);
lean_dec_ref(v_as_3811_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(lean_object* v_tac_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v_env_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3819_ = lean_st_ref_get(v___y_3817_);
v_env_3823_ = lean_ctor_get(v___x_3819_, 0);
lean_inc_ref(v_env_3823_);
lean_dec(v___x_3819_);
v___x_3824_ = lean_box(1);
v___x_3825_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3823_, v_tac_3816_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v___x_3826_; lean_object* v_toEnvExtension_3827_; lean_object* v_asyncMode_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3826_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3827_ = lean_ctor_get(v___x_3826_, 0);
v_asyncMode_3828_ = lean_ctor_get(v_toEnvExtension_3827_, 2);
v___x_3829_ = lean_box(0);
v___x_3830_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3824_, v___x_3826_, v_env_3823_, v_asyncMode_3828_, v___x_3829_);
v___x_3831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3830_, v_tac_3816_);
lean_dec(v_tac_3816_);
lean_dec(v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
else
{
lean_object* v_val_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3861_; 
v_val_3833_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3835_ = v___x_3825_;
v_isShared_3836_ = v_isSharedCheck_3861_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_val_3833_);
lean_dec(v___x_3825_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3861_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3837_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3838_ = 0;
v___x_3839_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3824_, v___x_3837_, v_env_3823_, v_val_3833_, v___x_3838_);
lean_dec(v_val_3833_);
lean_dec_ref(v_env_3823_);
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_array_get_size(v___x_3839_);
v___x_3842_ = lean_nat_dec_lt(v___x_3840_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_dec_ref(v___x_3839_);
lean_del_object(v___x_3835_);
lean_dec(v_tac_3816_);
goto v___jp_3820_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v___x_3843_ = lean_unsigned_to_nat(1u);
v___x_3844_ = lean_nat_sub(v___x_3841_, v___x_3843_);
v___x_3845_ = lean_nat_dec_le(v___x_3840_, v___x_3844_);
if (v___x_3845_ == 0)
{
lean_dec(v___x_3844_);
lean_dec_ref(v___x_3839_);
lean_del_object(v___x_3835_);
lean_dec(v_tac_3816_);
goto v___jp_3820_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6_spec__9___closed__1));
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_tac_3816_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v___x_3839_, v___x_3847_, v___x_3840_, v___x_3844_);
lean_dec_ref(v___x_3847_);
lean_dec_ref(v___x_3839_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_del_object(v___x_3835_);
goto v___jp_3820_;
}
else
{
lean_object* v_val_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3860_; 
v_val_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3860_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_val_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3860_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_snd_3853_; lean_object* v___x_3855_; 
v_snd_3853_ = lean_ctor_get(v_val_3849_, 1);
lean_inc(v_snd_3853_);
lean_dec(v_val_3849_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 0, v_snd_3853_);
v___x_3855_ = v___x_3851_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_snd_3853_);
v___x_3855_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3857_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3855_);
v___x_3857_ = v___x_3835_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
}
}
}
v___jp_3820_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_tac_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_3862_, v___y_3863_);
lean_dec(v___y_3863_);
return v_res_3865_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__0_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3868_ = l_Lean_stringToMessageData(v___x_3867_);
return v___x_3868_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3871_ = l_Lean_stringToMessageData(v___x_3870_);
return v___x_3871_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3874_ = l_Lean_stringToMessageData(v___x_3873_);
return v___x_3874_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3877_ = l_Lean_stringToMessageData(v___x_3876_);
return v___x_3877_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_3880_ = l_Lean_stringToMessageData(v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v_name_3891_, lean_object* v_decl_3892_, lean_object* v_stx_3893_, uint8_t v_kind_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; uint8_t v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v_name_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; uint8_t v___x_4052_; uint8_t v___x_4053_; 
v___x_4052_ = 0;
v___x_4053_ = l_Lean_instBEqAttributeKind_beq(v_kind_3894_, v___x_4052_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
lean_dec(v_stx_3893_);
lean_dec(v_decl_3892_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
lean_dec_ref(v___x_3888_);
lean_dec(v___x_3887_);
v___x_4054_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__7___redArg(v_name_3891_, v_kind_3894_, v___y_3895_, v___y_3896_);
return v___x_4054_;
}
else
{
goto v___jp_4011_;
}
v___jp_3898_:
{
lean_object* v___x_3901_; lean_object* v_env_3902_; lean_object* v_nextMacroScope_3903_; lean_object* v_ngen_3904_; lean_object* v_auxDeclNGen_3905_; lean_object* v_traceState_3906_; lean_object* v_messages_3907_; lean_object* v_infoState_3908_; lean_object* v_snapshotTasks_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3925_; 
v___x_3901_ = lean_st_ref_take(v___y_3900_);
v_env_3902_ = lean_ctor_get(v___x_3901_, 0);
v_nextMacroScope_3903_ = lean_ctor_get(v___x_3901_, 1);
v_ngen_3904_ = lean_ctor_get(v___x_3901_, 2);
v_auxDeclNGen_3905_ = lean_ctor_get(v___x_3901_, 3);
v_traceState_3906_ = lean_ctor_get(v___x_3901_, 4);
v_messages_3907_ = lean_ctor_get(v___x_3901_, 6);
v_infoState_3908_ = lean_ctor_get(v___x_3901_, 7);
v_snapshotTasks_3909_ = lean_ctor_get(v___x_3901_, 8);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; 
v_unused_3926_ = lean_ctor_get(v___x_3901_, 5);
lean_dec(v_unused_3926_);
v___x_3911_ = v___x_3901_;
v_isShared_3912_ = v_isSharedCheck_3925_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_snapshotTasks_3909_);
lean_inc(v_infoState_3908_);
lean_inc(v_messages_3907_);
lean_inc(v_traceState_3906_);
lean_inc(v_auxDeclNGen_3905_);
lean_inc(v_ngen_3904_);
lean_inc(v_nextMacroScope_3903_);
lean_inc(v_env_3902_);
lean_dec(v___x_3901_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3925_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; lean_object* v_toEnvExtension_3914_; lean_object* v_asyncMode_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3913_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3914_ = lean_ctor_get(v___x_3913_, 0);
v_asyncMode_3915_ = lean_ctor_get(v_toEnvExtension_3914_, 2);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_decl_3892_);
lean_ctor_set(v___x_3916_, 1, v___y_3899_);
v___x_3917_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3913_, v_env_3902_, v___x_3916_, v_asyncMode_3915_, v___x_3887_);
v___x_3918_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__4_spec__6___closed__5);
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 5, v___x_3918_);
lean_ctor_set(v___x_3911_, 0, v___x_3917_);
v___x_3920_ = v___x_3911_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_nextMacroScope_3903_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_ngen_3904_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v_auxDeclNGen_3905_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v_traceState_3906_);
lean_ctor_set(v_reuseFailAlloc_3924_, 5, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3924_, 6, v_messages_3907_);
lean_ctor_set(v_reuseFailAlloc_3924_, 7, v_infoState_3908_);
lean_ctor_set(v_reuseFailAlloc_3924_, 8, v_snapshotTasks_3909_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_st_ref_set(v___y_3900_, v___x_3920_);
v___x_3922_ = lean_box(0);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
}
}
v___jp_3927_:
{
lean_object* v___x_3931_; lean_object* v_a_3932_; 
lean_inc(v_decl_3892_);
v___x_3931_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_decl_3892_, v___y_3930_);
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v___x_3931_);
if (lean_obj_tag(v_a_3932_) == 1)
{
lean_object* v_val_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref(v___y_3928_);
lean_dec(v___x_3887_);
v_val_3933_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_val_3933_);
lean_dec_ref(v_a_3932_);
v___x_3934_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_3935_ = 0;
v___x_3936_ = l_Lean_MessageData_ofConstName(v_decl_3892_, v___x_3935_);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3934_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_stringToMessageData(v_val_3933_);
v___x_3941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3939_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_3943_, v___y_3929_, v___y_3930_);
return v___x_3944_;
}
else
{
lean_dec(v_a_3932_);
v___y_3899_ = v___y_3928_;
v___y_3900_ = v___y_3930_;
goto v___jp_3898_;
}
}
v___jp_3945_:
{
lean_object* v___x_3949_; lean_object* v_env_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_st_ref_get(v___y_3948_);
v_env_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc_ref(v_env_3950_);
lean_dec(v___x_3949_);
lean_inc(v_decl_3892_);
v___x_3951_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3950_, v_decl_3892_);
if (lean_obj_tag(v___x_3951_) == 1)
{
lean_object* v_val_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec_ref(v___y_3946_);
lean_dec(v___x_3887_);
v_val_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_val_3952_);
lean_dec_ref(v___x_3951_);
v___x_3953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3954_ = 0;
v___x_3955_ = l_Lean_MessageData_ofConstName(v_decl_3892_, v___x_3954_);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3953_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__1_00___x40_Lean_Parser_Tactic_Doc_1176478476____hygCtx___hyg_2_);
v___x_3958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = l_Lean_MessageData_ofConstName(v_val_3952_, v___x_3954_);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3958_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v___x_3953_);
v___x_3962_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3893_, v___x_3961_, v___y_3947_, v___y_3948_);
lean_dec(v_stx_3893_);
return v___x_3962_;
}
else
{
lean_dec(v___x_3951_);
lean_dec(v_stx_3893_);
v___y_3928_ = v___y_3946_;
v___y_3929_ = v___y_3947_;
v___y_3930_ = v___y_3948_;
goto v___jp_3927_;
}
}
v___jp_3963_:
{
lean_object* v___x_3968_; lean_object* v_env_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_st_ref_get(v___y_3967_);
v_env_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc_ref(v_env_3969_);
lean_dec(v___x_3968_);
v___x_3970_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3969_, v_decl_3892_);
lean_dec_ref(v_env_3969_);
if (lean_obj_tag(v___x_3970_) == 1)
{
lean_object* v_val_3971_; lean_object* v___x_3972_; lean_object* v_env_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
lean_dec_ref(v___y_3965_);
lean_dec(v___x_3887_);
v_val_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_val_3971_);
lean_dec_ref(v___x_3970_);
v___x_3972_ = lean_st_ref_get(v___y_3967_);
v_env_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc_ref(v_env_3973_);
lean_dec(v___x_3972_);
v___x_3974_ = l_Lean_Environment_allImportedModuleNames(v_env_3973_);
lean_dec_ref(v_env_3973_);
v___x_3975_ = lean_array_get_size(v___x_3974_);
v___x_3976_ = lean_nat_dec_lt(v_val_3971_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v___x_3974_);
lean_dec(v_val_3971_);
v___x_3977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3978_ = l_Lean_MessageData_ofConstName(v_decl_3892_, v___y_3964_);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3893_, v___x_3981_, v___y_3966_, v___y_3967_);
lean_dec(v_stx_3893_);
return v___x_3982_;
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3983_ = lean_array_fget(v___x_3974_, v_val_3971_);
lean_dec(v_val_3971_);
lean_dec_ref(v___x_3974_);
v___x_3984_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_3985_ = l_Lean_MessageData_ofConstName(v_decl_3892_, v___y_3964_);
v___x_3986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = l_Lean_MessageData_ofName(v___x_3983_);
v___x_3990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3893_, v___x_3992_, v___y_3966_, v___y_3967_);
lean_dec(v_stx_3893_);
return v___x_3993_;
}
}
else
{
lean_dec(v___x_3970_);
v___y_3946_ = v___y_3965_;
v___y_3947_ = v___y_3966_;
v___y_3948_ = v___y_3967_;
goto v___jp_3945_;
}
}
v___jp_3994_:
{
lean_object* v___x_3998_; lean_object* v_env_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; 
v___x_3998_ = lean_st_ref_get(v___y_3997_);
v_env_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc_ref(v_env_3999_);
lean_dec(v___x_3998_);
v___x_4000_ = 0;
lean_inc(v_decl_3892_);
v___x_4001_ = l_Lean_Environment_find_x3f(v_env_3999_, v_decl_3892_, v___x_4000_);
if (lean_obj_tag(v___x_4001_) == 0)
{
v___y_3946_ = v_name_3995_;
v___y_3947_ = v___y_3996_;
v___y_3948_ = v___y_3997_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_4002_; lean_object* v_env_4003_; uint8_t v___x_4004_; 
lean_dec_ref(v___x_4001_);
v___x_4002_ = lean_st_ref_get(v___y_3997_);
v_env_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc_ref(v_env_4003_);
lean_dec(v___x_4002_);
v___x_4004_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_4003_, v_decl_3892_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_dec_ref(v_name_3995_);
lean_dec(v___x_3887_);
v___x_4005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4006_ = l_Lean_MessageData_ofConstName(v_decl_3892_, v___x_4000_);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = l_Lean_throwErrorAt___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__5___redArg(v_stx_3893_, v___x_4009_, v___y_3996_, v___y_3997_);
lean_dec(v_stx_3893_);
return v___x_4010_;
}
else
{
v___y_3964_ = v___x_4000_;
v___y_3965_ = v_name_3995_;
v___y_3966_ = v___y_3996_;
v___y_3967_ = v___y_3997_;
goto v___jp_3963_;
}
}
}
v___jp_4011_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4012_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__10_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4013_ = l_Lean_Name_mkStr4(v___x_3888_, v___x_3889_, v___x_4012_, v___x_3890_);
lean_inc(v_stx_3893_);
v___x_4014_ = l_Lean_Syntax_isOfKind(v_stx_3893_, v___x_4013_);
lean_dec(v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v_stx_3893_);
lean_dec(v_decl_3892_);
lean_dec(v___x_3887_);
v___x_4015_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4016_ = l_Lean_MessageData_ofName(v_name_3891_);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4017_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4019_, v___y_3895_, v___y_3896_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
else
{
lean_object* v___x_4029_; lean_object* v_name_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4029_ = lean_unsigned_to_nat(1u);
v_name_4030_ = l_Lean_Syntax_getArg(v_stx_3893_, v___x_4029_);
v___x_4031_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__11_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4030_);
v___x_4032_ = l_Lean_Syntax_isOfKind(v_name_4030_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; uint8_t v___x_4034_; 
v___x_4033_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1___closed__13_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
lean_inc(v_name_4030_);
v___x_4034_ = l_Lean_Syntax_isOfKind(v_name_4030_, v___x_4033_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v_name_4030_);
lean_dec(v_stx_3893_);
lean_dec(v_decl_3892_);
lean_dec(v___x_3887_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__12_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4036_ = l_Lean_MessageData_ofName(v_name_3891_);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__14_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4039_, v___y_3895_, v___y_3896_);
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
lean_dec(v_name_3891_);
v___x_4049_ = l_Lean_TSyntax_getId(v_name_4030_);
lean_dec(v_name_4030_);
v___x_4050_ = l_Lean_Name_toString(v___x_4049_, v___x_4032_);
v_name_3995_ = v___x_4050_;
v___y_3996_ = v___y_3895_;
v___y_3997_ = v___y_3896_;
goto v___jp_3994_;
}
}
else
{
lean_object* v___x_4051_; 
lean_dec(v_name_3891_);
v___x_4051_ = l_Lean_TSyntax_getString(v_name_4030_);
lean_dec(v_name_4030_);
v_name_3995_ = v___x_4051_;
v___y_3996_ = v___y_3895_;
v___y_3997_ = v___y_3896_;
goto v___jp_3994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v___x_4055_, lean_object* v___x_4056_, lean_object* v___x_4057_, lean_object* v___x_4058_, lean_object* v_name_4059_, lean_object* v_decl_4060_, lean_object* v_stx_4061_, lean_object* v_kind_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v_kind_boxed_4066_; lean_object* v_res_4067_; 
v_kind_boxed_4066_ = lean_unbox(v_kind_4062_);
v_res_4067_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(v___x_4055_, v___x_4056_, v___x_4057_, v___x_4058_, v_name_4059_, v_decl_4060_, v_stx_4061_, v_kind_boxed_4066_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4067_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = lean_unsigned_to_nat(3374007381u);
v___x_4080_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__22_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4081_ = l_Lean_Name_num___override(v___x_4080_, v___x_4079_);
return v___x_4081_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__24_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4083_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__4_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4084_ = l_Lean_Name_str___override(v___x_4083_, v___x_4082_);
return v___x_4084_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__26_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_));
v___x_4086_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__5_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4087_ = l_Lean_Name_str___override(v___x_4086_, v___x_4085_);
return v___x_4087_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_unsigned_to_nat(2u);
v___x_4089_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__6_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4090_ = l_Lean_Name_num___override(v___x_4089_, v___x_4088_);
return v___x_4090_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4092_; lean_object* v___x_4093_; lean_object* v_name_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4092_ = 2;
v___x_4093_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__8_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v_name_4094_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__1_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4095_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__7_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4096_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v_name_4094_);
lean_ctor_set(v___x_4096_, 2, v___x_4093_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*3, v___x_4092_);
return v___x_4096_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4097_; lean_object* v___f_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___f_4097_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__2_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___f_4098_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__3_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_));
v___x_4099_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__9_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v___f_4098_);
lean_ctor_set(v___x_4100_, 2, v___f_4097_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___closed__10_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_);
v___x_4103_ = l_Lean_registerBuiltinAttribute(v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2____boxed(lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2_();
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(lean_object* v_tac_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___redArg(v_tac_4106_, v___y_4108_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0___boxed(lean_object* v_tac_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0(v_tac_4111_, v___y_4112_, v___y_4113_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_4116_, lean_object* v_k_4117_, lean_object* v_x_4118_, lean_object* v_x_4119_, lean_object* v_x_4120_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4116_, v_k_4117_, v_x_4118_, v_x_4119_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_4122_, lean_object* v_k_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_, lean_object* v_x_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_3374007381____hygCtx___hyg_2__spec__0_spec__0(v_as_4122_, v_k_4123_, v_x_4124_, v_x_4125_, v_x_4126_);
lean_dec_ref(v_k_4123_);
lean_dec_ref(v_as_4122_);
return v_res_4127_;
}
}
static lean_object* _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__0));
v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(lean_object* v_catName_4131_, lean_object* v_declName_4132_, uint8_t v___builtIn_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; uint8_t v___x_4138_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4176_; lean_object* v___y_4177_; 
v___x_4137_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_isTactic___closed__1));
v___x_4138_ = lean_name_eq(v_catName_4131_, v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4188_; lean_object* v_env_4196_; lean_object* v___x_4197_; 
v___x_4188_ = lean_st_ref_get(v___y_4135_);
v_env_4196_ = lean_ctor_get(v___x_4188_, 0);
lean_inc_ref(v_env_4196_);
lean_dec(v___x_4188_);
lean_inc(v_declName_4132_);
v___x_4197_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4196_, v_declName_4132_);
if (lean_obj_tag(v___x_4197_) == 0)
{
if (v___x_4138_ == 0)
{
v___y_4176_ = v___y_4134_;
v___y_4177_ = v___y_4135_;
goto v___jp_4175_;
}
else
{
goto v___jp_4189_;
}
}
else
{
lean_dec_ref(v___x_4197_);
goto v___jp_4189_;
}
v___jp_4189_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4190_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4191_ = l_Lean_MessageData_ofConstName(v_declName_4132_, v___x_4138_);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4194_, v___y_4134_, v___y_4135_);
return v___x_4195_;
}
}
else
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_dec(v_declName_4132_);
v___x_4198_ = lean_box(0);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
v___jp_4139_:
{
lean_object* v___x_4142_; lean_object* v_env_4143_; lean_object* v___x_4144_; lean_object* v_toEnvExtension_4145_; lean_object* v_asyncMode_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4142_ = lean_st_ref_get(v___y_4141_);
v_env_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc_ref(v_env_4143_);
lean_dec(v___x_4142_);
v___x_4144_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4145_ = lean_ctor_get(v___x_4144_, 0);
v_asyncMode_4146_ = lean_ctor_get(v_toEnvExtension_4145_, 2);
v___x_4147_ = lean_box(1);
v___x_4148_ = lean_box(0);
v___x_4149_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4147_, v___x_4144_, v_env_4143_, v_asyncMode_4146_, v___x_4148_);
v___x_4150_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4149_, v_declName_4132_);
lean_dec(v___x_4149_);
if (lean_obj_tag(v___x_4150_) == 1)
{
lean_object* v_val_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_val_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_val_4151_);
lean_dec_ref(v___x_4150_);
v___x_4152_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4153_ = l_Lean_MessageData_ofConstName(v_declName_4132_, v___x_4138_);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1_once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___closed__1);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_stringToMessageData(v_val_4151_);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v___x_4152_);
v___x_4160_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4159_, v___y_4140_, v___y_4141_);
return v___x_4160_;
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec(v___x_4150_);
lean_dec(v_declName_4132_);
v___x_4161_ = lean_box(0);
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
}
v___jp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4166_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__2___closed__1);
v___x_4167_ = l_Lean_MessageData_ofConstName(v_declName_4132_, v___x_4138_);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_obj_once(&l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_, &l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn___lam__2___closed__16_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2_);
v___x_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = l_Lean_throwError___at___00__private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_710499956____hygCtx___hyg_2__spec__0___redArg(v___x_4170_, v___y_4164_, v___y_4165_);
return v___x_4171_;
}
v___jp_4172_:
{
if (v___x_4138_ == 0)
{
v___y_4140_ = v___y_4173_;
v___y_4141_ = v___y_4174_;
goto v___jp_4139_;
}
else
{
v___y_4164_ = v___y_4173_;
v___y_4165_ = v___y_4174_;
goto v___jp_4163_;
}
}
v___jp_4175_:
{
lean_object* v___x_4178_; lean_object* v_env_4179_; lean_object* v___x_4180_; lean_object* v_toEnvExtension_4181_; lean_object* v_asyncMode_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4178_ = lean_st_ref_get(v___y_4177_);
v_env_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc_ref(v_env_4179_);
lean_dec(v___x_4178_);
v___x_4180_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4181_ = lean_ctor_get(v___x_4180_, 0);
v_asyncMode_4182_ = lean_ctor_get(v_toEnvExtension_4181_, 2);
v___x_4183_ = lean_box(1);
v___x_4184_ = lean_box(0);
v___x_4185_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4183_, v___x_4180_, v_env_4179_, v_asyncMode_4182_, v___x_4184_);
v___x_4186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4185_, v_declName_4132_);
lean_dec(v___x_4185_);
if (lean_obj_tag(v___x_4186_) == 1)
{
lean_object* v_val_4187_; 
v_val_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_val_4187_);
lean_dec_ref(v___x_4186_);
if (lean_obj_tag(v_val_4187_) == 0)
{
lean_dec_ref(v_val_4187_);
if (v___x_4138_ == 0)
{
v___y_4164_ = v___y_4176_;
v___y_4165_ = v___y_4177_;
goto v___jp_4163_;
}
else
{
v___y_4173_ = v___y_4176_;
v___y_4174_ = v___y_4177_;
goto v___jp_4172_;
}
}
else
{
v___y_4173_ = v___y_4176_;
v___y_4174_ = v___y_4177_;
goto v___jp_4172_;
}
}
else
{
lean_dec(v___x_4186_);
v___y_4140_ = v___y_4176_;
v___y_4141_ = v___y_4177_;
goto v___jp_4139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0___boxed(lean_object* v_catName_4200_, lean_object* v_declName_4201_, lean_object* v___builtIn_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
uint8_t v___builtIn_boxed_4206_; lean_object* v_res_4207_; 
v___builtIn_boxed_4206_ = lean_unbox(v___builtIn_4202_);
v_res_4207_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___lam__0(v_catName_4200_, v_declName_4201_, v___builtIn_boxed_4206_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v_catName_4200_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4211_; lean_object* v___x_4212_; 
v___f_4211_ = ((lean_object*)(l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_tacticDocsOnTactics___closed__0));
v___x_4212_ = l_Lean_Parser_registerParserAttributeHook(v___f_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2____boxed(lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn_00___x40_Lean_Parser_Tactic_Doc_2735967850____hygCtx___hyg_2_();
return v_res_4214_;
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
